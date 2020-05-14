/*
 * This file is part of Sloth, an SMT solver for strings.
 * Copyright (C) 2018  Matthew Hague, Philipp Ruemmer
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

package strsolver

import strsolver.preprop.{
  AllocTTerm,
  AtomicStateAutomaton,
  Automaton,
  BricsAutomaton,
  ConcatPreOp,
  Exploration,
  IndexOfPreOp,
  LengthPreOp,
  PreOp,
  RRFunsToTransducer,
  ReplaceAllPreOp,
  ReplaceAllPreOpW,
  ReplacePreOp,
  ReplacePreOpW,
  ReversePreOp,
  StoreLC,
  SubStringPreOp,
  Transducer,
  TransducerPreOp
}
import ap.SimpleAPI
import ap.terfor.{OneTerm, TerForConvenience, Term, TermOrder}
import ap.terfor.preds.PredConj
import ap.types.Sort
import ap.proof.goal.Goal
import ap.basetypes.IdealInt
import ap.parser.IExpression.GeqZ
import ap.parser.{IConstant, IExpression, ITerm, Internal2InputAbsy}
import ap.terfor.linearcombination.{LinearCombination, LinearCombination2}
import dk.brics.automaton.{RegExp, Automaton => BAutomaton}

import scala.collection.breakOut
import scala.collection.mutable.{
  ArrayBuffer,
  HashMap => MHashMap,
  HashSet => MHashSet
}

class PrepropSolver {

  import StringTheory.{
    member,
    replaceall,
    replaceallre,
    replace,
    replacere,
    reverse,
    wordEps,
    wordCat,
    wordChar,
    wordDiff,
    wordLen,
    // hu zi add -----------------------------------------------
    substring,
    indexof,
    str_contains,
    str_prefixof,
    str_at,
    // hu zi add -----------------------------------------------
    rexEmpty,
    rexEps,
    rexSigma,
    rexStar,
    rexUnion,
    rexChar,
    rexCat,
    rexNeg,
    rexRange,
    FunPred
  }

  val rexOps = Set(
    rexEmpty,
    rexEps,
    rexSigma,
    rexStar,
    rexUnion,
    rexChar,
    rexCat,
    rexNeg,
    rexRange
  )

  private val p = StringTheory.functionPredicateMap

  def findStringModel(goal: Goal): Option[Map[Term, List[Int]]] = {
    val atoms = goal.facts.predConj
    // 将输入中的整数约束提取出来
    val inputIntFormula = goal.facts.arithConj

    IntConstraintStore.setFormula(inputIntFormula)
    IntConstraintStore.setOrder(goal.order)
    implicit val order = goal.order
    val regex2AFA = new Regex2AFA(atoms)
    // P0 = length(x), then store (x, P0) to lenVar
    val lenVar = new MHashMap[Term, Term]()

    val containsLength = !(atoms positiveLitsWithPred p(wordLen)).isEmpty ||
      !(atoms positiveLitsWithPred p(substring)).isEmpty ||
      !(atoms positiveLitsWithPred p(indexof)).isEmpty ||
      !(atoms positiveLitsWithPred p(str_at)).isEmpty

    // all constant term in atoms, store their value in Seq[Int]
    val concreteWords = new MHashMap[Term, Seq[Int]]
    findConcreteWords(atoms) match {
      case Some(w) => concreteWords ++= w
      case None    => return None
    }

    // handle P0 != "a"
    val regexes = new ArrayBuffer[(Term, Automaton)] // all the res and arg aut
    inputIntFormula.negativeEqs.foreach {
      case lb: LinearCombination2 => {
        val t0 = LinearCombination(lb.getTerm(0), order)
        val t1 = LinearCombination(lb.getTerm(1), order)
        if (concreteWords.contains(t0)) {
          val str = concreteWords(t0).map(_.toChar).mkString
          regexes += ((t1, !BricsAutomaton.fromString(str)))
        } else if (concreteWords.contains(t1)) {
          val str = concreteWords(t1).map(_.toChar).mkString
          regexes += ((t0, !BricsAutomaton.fromString(str)))
        }
      }
      case _ =>
    }

    // extract regex constraints and function applications from the
    // literals
    val funApps = new ArrayBuffer[(PreOp, Seq[Term], Term)] // all the funciton except length and indexof
    val intFunApps = new ArrayBuffer[(PreOp, Seq[Term], Term)] // length and indexof funciton
    //    // (res, i, j) store res and two substring int,
    //    // to handle "" = substr(x, i, j), j<i. Or fasten unsat substring situation
    //    val substrInt = new MHashSet[(Term, Term, Term)]()
    //    // for other func ""=func(parameters), which implys the constraints is unsat
    //    val notSubstrNull = new MHashSet[Term]()
    //    // for example: 0 = length(x), x = substring(y, i, j), we can just add intconstraints i>=j
    //    // we store the term x in buffer zeroLen
    //    val zeroLen = new ArrayBuffer[Term]()
    //    for(a <- atoms.positiveLits) a.pred match {
    //      case FunPred(`substring`) => {
    //        substrInt += ((a(3), a(1), a(2)));
    //      }
    //      case FunPred(`wordLen`) => {
    //        if (a(1).isZero)
    //          zeroLen += a(0)
    //      }
    //      case `str_contains` => {
    //        if(concreteWords.contains(a.last) && concreteWords(a.last)!=List())
    //          notSubstrNull += a.head
    //      }
    //      case _ => {
    //        //TODO
    //      }
    //    }

    // handle wordlen firstly
    for (a <- atoms.positiveLits) a.pred match {
      case FunPred(`wordLen`) => {
        if (a(1).isZero) {
          lenVar += ((a(0), LinearCombination.ZERO))
          regexes += ((a(0), BricsAutomaton fromString ""))
          //              return None // unsat
        } else {
          lenVar += ((a(0), a(1)))
          intFunApps += (
            (
              LengthPreOp(Internal2InputAbsy(a(1))),
              List(a(0)),
              a(1)
            )
          )
        }
      }
      case _ => //nothing
    }
    for (a <- atoms.positiveLits) a.pred match {
      case FunPred(`wordChar` | `wordEps`) if concreteWords contains a.last =>
      // nothing, can be ignored
      case FunPred(`wordCat`) if a forall { t =>
            concreteWords contains t
          } =>
      // nothing, can be ignored
      case `member` =>
        regexes += ((a.head, BricsAutomaton(a.last, atoms)))
      // huzi add----------------------------------------------------------
      case `str_contains` => {
        if (concreteWords.contains(a.last)) {
          val str = concreteWords(a.last).map(_.toChar).mkString
          println("str.contains(" + a.head + "," + str + ")")
          val tmpAut = BricsAutomaton.fromString(str)
          val anyStrAut1 = BAutomaton.makeAnyString
          val anyStrAut2 = BAutomaton.makeAnyString
          regexes += (
            (
              a.head,
              BricsAutomaton.concat(
                List(anyStrAut1, tmpAut.underlying, anyStrAut2)
              )
            )
          )
        } else {
          println("str_contains not -----------------concreate word")
          println("unknow")
          System.exit(1)
        }
      }

      case `str_prefixof` => {
        println("a is " + a)
        println("a.head is " + a.head)
        if (concreteWords.contains(a.head)) {
          println("concreate word " + concreteWords(a.head))
          val str = concreteWords(a.head).map(_.toChar).mkString
          println("str.prefix(" + a.last + "," + str + ")")
          val tmpAut = BricsAutomaton.fromString(str)
          val anyStrAut = BAutomaton.makeAnyString
          regexes += (
            (
              a.last,
              BricsAutomaton.concat(List(tmpAut.underlying, anyStrAut))
            )
          )
        } else {
          println("str_prefixof not -----------------concreate word")
          println("unknow")
          System.exit(1)
        }
      }
      // huzi add----------------------------------------------------------

      case FunPred(`wordCat`) =>
        funApps += ((ConcatPreOp, List(a(0), a(1)), a(2)))

      // huzi modify ------------------------------------------------------------------------
      // TODO : when replacement result is empty string ""
      // design parameter of ReplacePreOpW、 ReplaceAllPreOpW
      case FunPred(`replaceall`) => {
        val b = (regex2AFA buildStrings a(1)).next
        if (concreteWords contains (a(2))) {
          // println("handle replaceall func with replacement of concreteword")
          val word = (regex2AFA buildStrings a(2)).next.map(_.left.get)
          funApps += ((ReplaceAllPreOpW(b, word), List(a(0), a(2)), a(3)))
        } else {
          printf(
            "can not handle this kind of replace( replacement is not concreteword )\n"
          )
          printf("unknow\n")
          return Some(Map())
        }
      }
      case FunPred(`replace`) => {
        val b = (regex2AFA buildStrings a(1)).next
        if (concreteWords contains (a(2))) {
          // println("handle replace func with replacement of concreteword")
          val word = (regex2AFA buildStrings a(2)).next.map(_.left.get)
          funApps += ((ReplacePreOpW(b, word), List(a(0), a(2)), a(3)))
        } else {
          printf(
            "can not handle this kind of replace( replacement is not concreteword )\n"
          )
          printf("unknow\n")
          return Some(Map())
        }
      }
      case FunPred(`replaceallre`) => {
        regexValue(a(1), regex2AFA) match {
          case Left(w) =>
            if (concreteWords contains (a(2))) {
              // println("handle replaceall-re func with replacement of concreteword")
              val word = (regex2AFA buildStrings a(2)).next.map(_.left.get)
              funApps += ((ReplaceAllPreOpW(w, word), List(a(0), a(2)), a(3)))
            } else {
              printf(
                "can not handle this kind of replace( replacement is not concreteword )\n"
              )
              printf("unknow\n")
              return Some(Map())
            }
          case Right(aut) =>
            if (concreteWords contains (a(2))) {
              // println("handle replace-re func with replacement of concreteword")
              val word = (regex2AFA buildStrings a(2)).next.map(_.left.get)
              funApps += ((ReplaceAllPreOpW(aut, word), List(a(0), a(2)), a(3)))
            } else {
              printf(
                "can not handle this kind of replace( replacement is not concreteword )\n"
              )
              printf("unknow\n")
              return Some(Map())
            }
        }
      }
      case FunPred(`replacere`) => {
        regexValue(a(1), regex2AFA) match {
          case Left(w) =>
            if (concreteWords contains (a(2))) {
              // println("handle replace-re func with replacement of concreteword")
              val word = (regex2AFA buildStrings a(2)).next.map(_.left.get)
              funApps += ((ReplacePreOpW(w, word), List(a(0), a(2)), a(3)))
            } else {
              printf(
                "can not handle this kind of replace( replacement is not concreteword )\n"
              )
              printf("unknow\n")
              return Some(Map())
            }
          case Right(aut) =>
            if (concreteWords contains (a(2))) {
              // println("handle replace-re func with replacement of concreteword")
              val word = (regex2AFA buildStrings a(2)).next.map(_.left.get)
              funApps += ((ReplacePreOpW(aut, word), List(a(0), a(2)), a(3)))
            } else {
              printf(
                "can not handle this kind of replace( replacement is not concreteword )\n"
              )
              printf("unknow\n")
              return Some(Map())
            }
        }
      }
      // huzi modify -------------------------------------------------------------------------

      // hu zi add -------------------------------------------------------------------
      case FunPred(`substring`) => {
        // tmpTerm(0) is x len, tmpTerm(1) is res len
        val tmpTerm = new ArrayBuffer[Term]()
        // x len
        if (lenVar.contains(a(0)))
          tmpTerm += lenVar(a(0))
        else {
          tmpTerm += AllocTTerm()
          intFunApps += (
            (
              LengthPreOp(Internal2InputAbsy(tmpTerm(0))),
              List(a(0)),
              tmpTerm(0)
            )
          )
          lenVar += ((a(0), tmpTerm(0)))
        } // x len  end
        // res len
        if (lenVar.contains(a(3)))
          tmpTerm += lenVar(a(3))
        else {
          tmpTerm += AllocTTerm()
          intFunApps += (
            (
              LengthPreOp(Internal2InputAbsy(tmpTerm(1))),
              List(a(3)),
              tmpTerm(1)
            )
          )
          lenVar += ((a(3), tmpTerm(1)))
        } // res len  end
        funApps += (
          (
            SubStringPreOp(a(1), a(2), tmpTerm(0), tmpTerm(1)),
            List(a(0), a(1), a(2)),
            a(3)
          )
        )
      }
      case FunPred(`indexof`) => {
        println("handle indexof")
        if (!concreteWords.contains(a(1)))
          throw new Exception("indexof pattern is not a concrete word ")
        val u = (regex2AFA buildStrings a(1)).next.map(_.left.get.toChar)
        if (u.size == 0) {
          // pattern is ""
          // val t : Term = AllocTTerm()
          // val i = Internal2InputAbsy(a(3))
          // val j = Internal2InputAbsy(a(2))
          // val ti = Internal2InputAbsy(t)
          // intFunApps += ((LengthPreOp(Internal2InputAbsy(t)), List(a(0)), t))   // t = wordLen(a(0))
          // StoreLC.addFormula( ((i==j)&(j<=ti)) |
          //   ((i == -1)&(j>ti)))
          // cvc4 semantic
          return None // unsat
        } else {
          intFunApps += ((IndexOfPreOp(u, a(3), a(2)), List(a(0)), a(3)))
        }
      }
      case FunPred(`str_at`) => {
//        if(!lenVar.contains(a(0))) {
//          val t = AllocTTerm()
//          lenVar += ((a(0), t))
//          intFunApps += ((LengthPreOp(Internal2InputAbsy(t)), List(a(0)), t))
//          funApps += ((SubStringPreOp(a(1), OneTerm, t), List(a(0), a(1), OneTerm), a(2)))
//        }else{
//          val t = lenVar(a(0))
//          funApps += ((SubStringPreOp(a(1), OneTerm, t), List(a(0), a(1), OneTerm), a(2)))
//        }

        // tmpTerm(0) is x len, tmpTerm(1) is res len
        val tmpTerm = new ArrayBuffer[Term]()
        // x len
        if (lenVar.contains(a(0)))
          tmpTerm += lenVar(a(0))
        else {
          tmpTerm += AllocTTerm()
          intFunApps += (
            (
              LengthPreOp(Internal2InputAbsy(tmpTerm(0))),
              List(a(0)),
              tmpTerm(0)
            )
          )
          lenVar += ((a(0), tmpTerm(0)))
        } // x len  end
        // res len
        if (lenVar.contains(a(2)))
          tmpTerm += lenVar(a(2))
        else {
          tmpTerm += AllocTTerm()
          intFunApps += (
            (
              LengthPreOp(Internal2InputAbsy(tmpTerm(1))),
              List(a(2)),
              tmpTerm(1)
            )
          )
          lenVar += ((a(2), tmpTerm(1)))
        } // res len  end
        funApps += (
          (
            SubStringPreOp(a(1), OneTerm, tmpTerm(0), tmpTerm(1)),
            List(a(0), a(1), OneTerm),
            a(2)
          )
        )
      }

      // hu zi add -------------------------------------------------------------------
      case FunPred(`reverse`) =>
        funApps += ((ReversePreOp, List(a(0)), a(1)))
      case FunPred(f) if rexOps contains f =>
      // nothing
      case FunPred(f)
          if UserFunctionRegistry.isUserDefinedStringTheoryFun(f.name) =>
        funApps += (
          (
            UserFunctionRegistry.getPreOp(f.name).get,
            a.take(f.arity),
            a(f.arity)
          )
        )
      case pred if (RRFunsToTransducer get pred).isDefined =>
        funApps += (
          (
            TransducerPreOp(RRFunsToTransducer.get(pred).get),
            List(a(0)),
            a(1)
          )
        )
      case p if (StringTheory.predicates contains p) =>
      // Console.err.println("Warning: ignoring " + a)
      case _ =>
      // nothing
    }

    for (a <- atoms.negativeLits) a.pred match {
      case `member` =>
        regexes += ((a.head, !BricsAutomaton(a.last, atoms)))
      case `str_contains` => {
        if (concreteWords.contains(a.last)) {
          val str = concreteWords(a.last).map(_.toChar).mkString
          println("!str.contains(" + a.head + "," + str + ")")
          val tmpAut = BricsAutomaton.fromString(str)
          val anyStrAut1 = BAutomaton.makeAnyString
          val anyStrAut2 = BAutomaton.makeAnyString
          regexes += (
            (
              a.head,
              !BricsAutomaton.concat(
                List(anyStrAut1, tmpAut.underlying, anyStrAut2)
              )
            )
          )
        } else {
          println("str_contains not -----------------concreate word")
          println("unknow")
          System.exit(1)
        }
      }
      case `str_prefixof` => {
        println("a is " + a)
        println("a.head is " + a.head)
        if (concreteWords.contains(a.head)) {
          println("concreate word " + concreteWords(a.head))
          val str = concreteWords(a.head).map(_.toChar).mkString
          println("str.prefix(" + a.last + "," + str + ")")
          val tmpAut = BricsAutomaton.fromString(str)
          val anyStrAut = BAutomaton.makeAnyString
          regexes += (
            (
              a.last,
              !BricsAutomaton.concat(List(tmpAut.underlying, anyStrAut))
            )
          )
        } else {
          println("str_prefixof not -----------------concreate word")
          println("unknow")
          System.exit(1)
        }
      }
      case p if (StringTheory.predicates contains p) =>
        Console.err.println("Warning: ignoring !" + a)
      case _ =>
      // nothing
    }

    {
      var changed = true
      while (changed) {
        changed = false

        for (n <- (funApps.size - 1) to 0 by -1) {
          val (op, args, res) = funApps(n)
          if (args forall (concreteWords contains _)) {
            op.eval(args map concreteWords) match {
              case Some(newRes) =>
                (concreteWords get res) match {
                  case Some(oldRes) =>
                    if (newRes != oldRes)
                      return None
                  case None =>
                    concreteWords.put(res, newRes)
                }
              case None =>
                return None
            }
            funApps remove n
            changed = true
          }
        }
      }
    }

    // terms in regexes and funApps( both res and args involved)
    val interestingTerms =
      ((for ((t, _) <- regexes.iterator) yield t) ++
        (for ((_, args, res) <- funApps.iterator;
              t <- args.iterator ++ Iterator(res)) yield t)).toSet

    // add aut constraints to concreteWords in interestingTerms
    for (t <- interestingTerms)
      (concreteWords get t) match {
        case Some(w) => {
          if (w.size == 0) {
            //empty string
            regexes += ((t, BricsAutomaton fromString ("")))
          } else {
            val str: String = w.map(i => i.toChar)(breakOut)
            regexes += ((t, BricsAutomaton fromString str))
          }
        }
        case None =>
        // nothing
      }
    // regexes is initialConstraints in Exploration, from above, we known
    // that initialConstraints consists of "member" funciton and concreteword
    // in interestingTerms

    ////////////////////////////////////////////////////////////////////////////

    SimpleAPI.withProver { lengthProver =>
      val exploration =
        Exploration.lazyExp(
          funApps,
          intFunApps,
          concreteWords,
          regexes,
          containsLength
        )

      exploration.findModel match {
        case Some(model) =>
          Some(
            (model mapValues (_.toList)) ++
              (concreteWords mapValues (_.toList))
          )
        case None => None
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private object Inconsistent extends Exception

  private def findConcreteWords(atoms: PredConj): Option[Map[Term, Seq[Int]]] =
    try {
      val res = new MHashMap[Term, Seq[Int]]

      def assign(t: Term, w: Seq[Int]): Unit =
        (res get t) match {
          case Some(u) =>
            if (u != w)
              // inconsistent words
              throw Inconsistent
          case None =>
            res.put(t, w)
        }

      for (a <- atoms positiveLitsWithPred p(wordEps))
        assign(a.last, List())
      for (a <- atoms positiveLitsWithPred p(wordChar)) {
        if (!a.head.isConstant)
          throw new Exception("Cannot handle " + a)
        assign(a.last, List(a.head.constant.intValueSafe))
      }
      var oldSize = 0
      while (res.size > oldSize) {
        oldSize = res.size

        for (a <- atoms positiveLitsWithPred p(wordCat))
          if ((res contains a(0)) && (res contains a(1)))
            assign(a(2), res(a(0)) ++ res(a(1)))
      }

      // handle rex op for concrete word
      for (a <- atoms positiveLitsWithPred p(rexEps))
        assign(a.last, List())
      for (a <- atoms positiveLitsWithPred p(rexChar)) {
        if (!a.head.isConstant)
          throw new Exception("Cannot handle " + a)
        assign(a.last, List(a.head.constant.intValueSafe))
      }
      oldSize = 0
      while (res.size > oldSize) {
        oldSize = res.size

        for (a <- atoms positiveLitsWithPred p(rexCat))
          if ((res contains a(0)) && (res contains a(1)))
            assign(a(2), res(a(0)) ++ res(a(1)))
      }

      Some(res.toMap)
    } catch {
      case Inconsistent => None
    }

  /**
    * Translate term in a regex argument position into an automaton
    * returns a string if it detects only one word is accepted
    */
  private def regexValue(
      regex: Term,
      regex2AFA: Regex2AFA
  ): Either[String, AtomicStateAutomaton] = {
    val b = (regex2AFA buildStrings regex).next
    if (!b.isEmpty && b(0).isLeft) {
      // In this case we've been given a string regex and expect it
      // to start and end with / /
      // if it just defines one string, treat it as a replaceall
      // else treat it as true replaceall-re
      val stringB: String = b.map(_.left.get.toChar)(collection.breakOut)
      if (stringB(0) != '/' || stringB.last != '/')
        throw new IllegalArgumentException(
          "regex defined with a string argument expects the regular expression to start and end with /"
        )
      val sregex = stringB.slice(1, stringB.size - 1)
      val baut = new RegExp(sregex, RegExp.NONE).toAutomaton(true)
      val w = baut.getSingleton
      if (w != null)
        return Left(w)
      else
        return Right(new BricsAutomaton(baut))
    } else {
      return Right(BricsAutomaton(regex2AFA buildRegex regex))
    }
  }
}

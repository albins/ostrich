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

package strsolver.preprop

import java.io.{FileWriter, PrintWriter}

import strsolver.Regex2AFA
import com.typesafe.scalalogging.LazyLogging
import ap.SimpleAPI
import ap.terfor.{Term, ConstantTerm}
import ap.terfor.preds.PredConj
import ap.terfor.substitutions.ConstantSubst
import ap.parser.{
  IConstant,
  ITerm,
  InputAbsy2Internal,
  Internal2InputAbsy,
  IExpression,
  IFormula
}

import strsolver.preprop.MapGraph._

import dk.brics.automaton.{
  BasicAutomata,
  BasicOperations,
  RegExp,
  Transition,
  Automaton => BAutomaton,
  State => BState
}

import scala.collection.JavaConversions.{
  asScalaIterator,
  iterableAsScalaIterable
}
import scala.collection.mutable.{
  ArrayBuffer,
  HashMap => MHashMap,
  HashSet => MHashSet,
  LinkedHashSet => MLinkedHashSet,
  MultiMap => MMultiMap,
  Set => MSet,
  Map => MMap,
  Stack => MStack,
  TreeSet => MTreeSet,
  BitSet
}
import scala.collection.immutable.List
import java.util.{List => JList}

import scala.collection.JavaConverters._

import scala.language.postfixOps

object BricsAutomaton {
  private def toBAutomaton(aut: Automaton): BAutomaton = aut match {
    case that: BricsAutomaton =>
      that.underlying
    case that: AtomicStateAutomatonAdapter[_] =>
      toBAutomaton(that.internalise)
    case _ =>
      throw new IllegalArgumentException
  }

  def apply(c: Term, context: PredConj): BricsAutomaton = {
    val converter = new Regex2AFA(context)
    new BricsAutomaton(converter.buildBricsAut(c))
  }

  def apply(): BricsAutomaton = new BricsAutomaton(new BAutomaton)

  /**
    * Build brics automaton from a regular expression in brics format
    */
  def apply(pattern: String): BricsAutomaton =
    new BricsAutomaton(new RegExp(pattern).toAutomaton(true))

  /**
    * Build brics automaton that accepts exactly the given word
    */
  def fromString(str: String): BricsAutomaton =
    new BricsAutomaton(BasicAutomata makeString str)

//  def makeEmptyString() : BricsAutomaton =
//    new BricsAutomaton(BasicAutomata makeEmptyString())
  /**
    * A new automaton that accepts any string
    */
  def makeAnyString(): BricsAutomaton = {
//      new BricsAutomaton(BAutomaton.makeAnyString)
    val builder = new BricsAutomatonBuilder
    val initState = builder.getNewState
    val Sigma = builder.LabelOps.sigmaLabel
    builder.setInitialState(initState)
    builder.setAccept(initState, true)
    builder.addTransition(initState, Sigma, initState)
    builder.getAutomaton

  }

  // huzi add -------------------------------------------
  /**
    * concatenate
    */
  def concat(auts: List[BAutomaton]): Automaton = {
    val aut = BasicOperations.concatenate(auts.asJava)
    aut.minimize()
    aut.restoreInvariant
    new BricsAutomaton(aut)
  }

  // get product of auts whose registers is NULL
  def productSpecially(auts: Seq[Automaton]): BricsAutomaton = {
    new BricsAutomaton(toBAutomaton(auts.reduceLeft(_ & _)))
  }

  val MaxSimultaneousProduct = 2

  def product(auts: Seq[BricsAutomaton]): BricsAutomaton = {
    if (auts.size == 0)
      return (BricsAutomaton.makeAnyString)

    if (auts.size == 1)
      return auts.head

    val firstSlice = auts
      .grouped(MaxSimultaneousProduct)
      .map(fullProduct(_))
      .toSeq

    if (firstSlice.size == 1)
      return firstSlice(0)
    else
      return product(firstSlice)
  }

  def fullProduct(auts: Seq[BricsAutomaton]): BricsAutomaton = {
    println(
      "Computing product of automata with sizes " + (auts map (_.states.size))
        .mkString(", ")
    )

    val head = auts.head
    val builder = head.getBuilder

    val registers = auts.flatMap(_.registers).toList

    val initState = builder.initialState
    // from new states to list of old
    val sMap = new MHashMap[head.State, List[Any]]
    // from list of old to new states
    val sMapRev = new MHashMap[List[Any], head.State]

    val initStates = (auts.map(_.initialState)).toList
    sMap += initState -> initStates
    sMapRev += initStates -> initState

    val worklist = new MStack[(head.State, List[Any])]
    worklist push ((initState, initStates))

    val seenlist = MHashSet[List[Any]]()
    seenlist += initStates

    builder.setAccept(initState, auts forall { aut =>
      aut.isAccept(aut.initialState)
    })

    var checkCnt = 0

    while (!worklist.isEmpty) {
      val (ps, ss) = worklist.pop()

      // collects transitions from (s, ss)
      // lbl = (min, max) is current range
      // vector is current vector
      // sp and ssp are s' and ss' (ss' is reversed for efficiency)
      // ss are elements of ss from which a transition is yet to be
      // searched
      def addTransitions(
          lbl: head.TLabel,
          vector: List[Int],
          ssp: List[Any],
          remAuts: List[BricsAutomaton],
          ss: List[Any]
      ): Unit = {
        checkCnt = checkCnt + 1
        if (checkCnt % 1000 == 0)
          ap.util.Timeout.check
        ss match {
          case Seq() => {
            val nextState = ssp.reverse
            if (!seenlist.contains(nextState)) {
              val nextPState = builder.getNewState
              val isAccept = (auts.iterator zip nextState.iterator) forall {
                case (aut, s) => aut.isAccept(s.asInstanceOf[aut.State])
              }
              builder.setAccept(nextPState, isAccept)
              sMap += nextPState -> nextState
              sMapRev += nextState -> nextPState
              worklist.push((nextPState, nextState))
              seenlist += nextState
            }
            val nextPState = sMapRev(nextState)
            // add vector
            builder.addTransition(ps, lbl, nextPState, vector)
          }
          case _state :: ssTail => {
            val aut :: autsTail = remAuts
            val state = _state.asInstanceOf[aut.State]

            aut.outgoingTransitions(state) foreach {
              case (s, nextLbl) => {
                val newLbl =
                  builder.LabelOps
                    .intersectLabels(lbl, nextLbl.asInstanceOf[head.TLabel])
                // this sort maybe wrong
                val vect = vector ::: aut.etaMap((state, nextLbl, s))
                for (l <- newLbl)
                  addTransitions(l, vect, s :: ssp, autsTail, ssTail)
              }
            }
          }
        }
      }

      addTransitions(
        builder.LabelOps.sigmaLabel,
        List(),
        List(),
        auts.toList,
        ss
      )
    }

    builder.removeBackwardsUnreachableStates()

    val res = builder.getAutomaton
    res.addEtaMaps(builder.etaMap)
    res.setRegisters(registers)

    val res2 = res.minimize
    println("Size of resulting automaton: " + res2.states.size)

    res2
  }
}

object BricsTLabelOps extends TLabelOps[(Char, Char)] {

  val vocabularyWidth: Int = 16 // really?

  /**
    * Check whether the given label accepts any letter
    */
  def isNonEmptyLabel(label: (Char, Char)): Boolean =
    label._1 <= label._2

  /**
    * Label accepting all letters
    */
  // val sigmaLabel : (Char, Char) =
  //   (Char.MinValue, Char.MaxValue)

  //huzi modify, ascii char
  val sigmaLabel: (Char, Char) =
    (Char.MinValue, Char.MaxValue)

  def singleton(a: Char) = (a, a)

  /**
    * Intersection of two labels
    */
  def intersectLabels(
      l1: (Char, Char),
      l2: (Char, Char)
  ): Option[(Char, Char)] = {
    Option((l1._1 max l2._1, l1._2 min l2._2)).filter(isNonEmptyLabel(_))
  }

  /**
    * True if labels overlap
    */
  def labelsOverlap(l1: (Char, Char), l2: (Char, Char)): Boolean = {
    val (min1, max1) = l1
    val (min2, max2) = l2
    (min2 <= max1 && max2 >= min1)
  }

  /**
    * Can l represent a?
    */
  def labelContains(a: Char, l: (Char, Char)): Boolean = {
    val (min, max) = l
    (min <= a && a <= max)
  }

  /**
    * Enumerate all letters accepted by a transition label
    */
  def enumLetters(label: (Char, Char)): Iterator[Int] =
    for (c <- (label._1 to label._2).iterator) yield c.toInt

  /**
    * Remove a given character from the label.  E.g. [1,10] - 5 is
    * [1,4],[6,10]
    */
  def subtractLetter(a: Char, lbl: (Char, Char)): Iterable[(Char, Char)] = {
    val (min, max) = lbl
    if (min <= a && a <= max) {
      // surely a cuter solution than this exists...
      var res = List[(Char, Char)]()
      if (min < a)
        res = (min, (a - 1).toChar) :: res
      if (a < max)
        res = ((a + 1).toChar, max) :: res
      res
    } else {
      Seq(lbl)
    }
  }

  /**
    * Shift characters by n, do not wrap.  E.g. [1,2].shift 3 = [4,5]
    */
  def shift(lbl: (Char, Char), n: Int): (Char, Char) = {
    val (cmin, cmax) = lbl
    (
      Math.max(Char.MinValue, cmin + n).toChar,
      Math.min(Char.MaxValue, cmax + n).toChar
    )
  }

  /**
    * Get representation of interval [min,max]
    */
  def interval(min: Char, max: Char): (Char, Char) = (min, max)
}

class BricsTLabelEnumerator(labels: Iterator[(Char, Char)])
    extends TLabelEnumerator[(Char, Char)] {

  /**
    * Keep track of disjoint labels for fast range lookups in
    * enumLabelOverlap.  Access with getDisjointLabels.
    */
  private lazy val disjointLabels: MTreeSet[(Char, Char)] =
    calculateDisjointLabels

  /**
    * Like disjoint labels but covers whole alphabet including internal
    * char.
    */
  private lazy val disjointLabelsComplete: List[(Char, Char)] =
    calculateDisjointLabelsComplete

  /**
    * Enumerate all labels with overlaps removed.
    * E.g. for min/max labels [1,3] [5,10] [8,15] would result in [1,3]
    * [5,8] [8,10] [10,15]
    */
  def enumDisjointLabels: Iterable[(Char, Char)] =
    disjointLabels.toIterable

  /**
    * Enumerate all labels with overlaps removed such that the whole
    * alphabet is covered (including internal characters)
    * E.g. for min/max labels [1,3] [5,10] [8,15] would result in [1,3]
    * [4,4] [5,7] [8,10] [11,15] [15,..]
    */
  def enumDisjointLabelsComplete: Iterable[(Char, Char)] =
    disjointLabelsComplete

  /**
    * iterate over the instances of lbls that overlap with lbl
    */
  def enumLabelOverlap(lbl: (Char, Char)): Iterable[(Char, Char)] = {
    val (lMin, lMax) = lbl
    disjointLabels
      .from((lMin, Char.MinValue))
      .to((lMax, Char.MaxValue))
      .toIterable
  }

  /**
    * Takes disjoint enumeration and splits it at the point defined by
    * Char.  E.g. [1,10] split at 5 is [1,4][5][6,10]
    */
  def split(a: Char): TLabelEnumerator[(Char, Char)] =
    new BricsTLabelEnumerator(disjointLabels.iterator ++ Iterator((a, a)))

  private def calculateDisjointLabels(): MTreeSet[(Char, Char)] = {
    val disjoint = new MTreeSet[(Char, Char)]()

    val mins = new MTreeSet[Char]
    val maxes = new MTreeSet[Char]
    for ((min, max) <- labels) {
      mins += min
      maxes += max
    }

    val imin = mins.iterator
    val imax = maxes.iterator

    if (!imin.hasNext)
      return disjoint

    var curMin = imin.next
    var nextMax = imax.next
    while (imin.hasNext) {
      val nextMin = imin.next
      if (nextMin <= nextMax) {
        disjoint += ((curMin, (nextMin - 1).toChar))
        curMin = nextMin
      } else {
        disjoint += ((curMin, nextMax))
        curMin = nextMin
        nextMax = imax.next
      }
    }

    disjoint += ((curMin, nextMax))
    curMin = (nextMax + 1).toChar

    while (imax.hasNext) {
      val nextMax = imax.next
      disjoint += ((curMin, nextMax))
      curMin = (nextMax + 1).toChar
    }

    disjoint
  }

  private def calculateDisjointLabelsComplete(): List[(Char, Char)] = {
    val labelsComp = disjointLabels.foldRight(List[(Char, Char)]()) {
      case ((min, max), Nil) => {
        // using Char.MaxValue since we include internal chars
        if (max < Char.MaxValue)
          List((min, max), ((max + 1).toChar, Char.MaxValue))
        else
          List((min, max))
      }
      case ((min, max), (minLast, maxLast) :: lbls) => {
        val minLastPrev = (minLast - 1).toChar
        if (max < minLastPrev)
          (min, max) :: ((max + 1).toChar, minLastPrev) :: (minLast, maxLast) :: lbls
        else
          (min, max) :: (minLast, maxLast) :: lbls
      }
    }
    if (Char.MinValue < labelsComp.head._1) {
      val nextMin = (labelsComp.head._1 - 1).toChar
      (Char.MinValue, nextMin) :: labelsComp
    } else {
      labelsComp
    }
  }
}

/**
  * Wrapper for the BRICS automaton class
  */
class BricsAutomaton(val underlying: BAutomaton)
    extends AtomicStateAutomaton
    with Graphable[BState, (Char, Char)]
    with RichGraph[BState, (Char, Char)]
    with LazyLogging {
  import BricsAutomaton.toBAutomaton

  type State = BState
  type TLabel = (Char, Char)
  type Node = State

  override val LabelOps = BricsTLabelOps

  override def toString: String = ap.DialogUtil.asString {
    println("/-----------------------------------------------")
    println("|                BricsAutomaton")

    registers match {
      case Seq() =>
      case regs  => println("| Registers:      " + (regs mkString ", ") + "")
    }

    val stateAr = states.toArray
    val stateIndex = stateAr.iterator.zipWithIndex.toMap

    println("| Initial state:  " + stateIndex(initialState))
    println(
      "| Final state(s): " +
        (for ((s, n) <- stateAr.iterator.zipWithIndex; if isAccept(s))
          yield n).mkString(", ")
    )

    for ((s, n) <- stateAr.iterator.zipWithIndex) {
      println("| State " + n)
      for ((t, l) <- outgoingTransitions(s)) {
        print("|   " + l + " -> " + stateIndex(t))
        if (!registers.isEmpty) {
          var prefix = "\t("
          for ((r, o) <- registers zip etaMap((s, l, t))) {
            print(prefix + r + " += " + o)
            prefix = "; "
          }
          print(")")
        }
        println
      }
    }
    println("\\-----------------------------------------------")
  }

  // hu zi add ---------------------------------------------------------------------------------------------------------------
//  val registers : ArrayBuffer[ITerm]= ArrayBuffer()  // or maybe ArrayBuffer[ConstantTerm]
  // registers += AllocRegisterTerm()  //debug
  // (q', σ, q, η) tuple, stored as a map
  val etaMap = new MHashMap[(State, TLabel, State), List[Int]]
  addEtaMapsDefault

  // FIXME: we will not always need these
  private val stateSeq = states.toIndexedSeq
  private lazy val state2Index = stateSeq.iterator.zipWithIndex.toMap

  private def fmtTransition(t: FromLabelTo) = {
    val (from, (labelMin, labelMax), to) = t

    s"(${state2Index(from)} -[${labelMin.toInt}, ${labelMax.toInt}]-> ${state2Index(to)})"
  }

  /**
    * get parikh iamge of BricsAutomaton
    */
  import ap.terfor.{
    Formula,
    Term,
    TerForConvenience,
    TermOrder,
    OneTerm,
    VariableTerm
  }
  import scala.collection.mutable.{
    BitSet => MBitSet,
    HashMap => MHashMap,
    HashSet => MHashSet,
    ArrayStack
  }
  import ap.terfor.linearcombination.LinearCombination
  import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
  import ap.basetypes.IdealInt
  import ap.PresburgerTools
  import scala.annotation.tailrec

  type FromLabelTo = (State, TLabel, State)

  def toDot: String = {
    val stateAr = states.toArray
    val stateIndex = stateAr.iterator.zipWithIndex.toMap

    val out = new StringBuilder()
    out ++= "digraph Automaton {\n"

    def addStatement(s: String) = out ++= s"\t${s};\n"

    addStatement("rankdir = LR")
    addStatement("node [shape = point,witdth=1]; qi")

    addStatement(s"qi -> ${stateIndex(initialState)}")

    for ((s, n) <- stateAr.iterator.zipWithIndex) {
      val acceptAnnot = if (isAccept(s)) {
        "shape=doublecircle, "
      } else {
        ""
      }
      addStatement(s"${n} [${acceptAnnot}label=${n}]")
      for ((t, l) <- outgoingTransitions(s)) {
        val registerPart = (registers zip etaMap((s, l, t)))
          .map { case (r, o) => s"${r} += ${o}" }
          .mkString(",\\l")

        val labelPart = s"${l._1.toInt}--${l._2.toInt}"

        val edgeLabel = "\"" + labelPart + "\\n" + registerPart.toString + "\""
        addStatement(s"${n} -> ${stateIndex(t)} [minlen=1,label=${edgeLabel}]")
      }
    }

    out ++= "}\n"
    out.toString
  }

  override def parikhImage: Formula = {

    val simpAut = this.makeLabelsUniform.minimize
    val newImage = simpAut.parikhImageNew
    val oldImage = simpAut.parikhImageOld

    SimpleAPI.withProver { p =>
      import p._
      registers foreach {
        case IConstant(c) => addConstantRaw(c)
      }
      implicit val o = order
      val reduced =
        PresburgerTools.elimQuantifiersWithPreds(Conjunction.conj(oldImage, o))

      addConclusion(
        Conjunction.conj(newImage, o) <=>
          Conjunction.conj(reduced, o)
      )
      if (??? != SimpleAPI.ProverStatus.Valid) {
        println(
          s"simplified new image: ${pp(simplify(asIFormula(Conjunction.conj(newImage, o))))}"
        )
        println(s"simplified old image: ${pp(simplify(asIFormula(reduced)))}")
        println(s"Countermodel: ${partialModel}")

        println("Automata:")
        println(this.toString)

        import java.io._
        val file = new File("problem-automata.dot")
        val bw = new BufferedWriter(new FileWriter(file))
        bw.write(this.toDot)
        bw.flush()
        assert(false)
      }

    }
    logger.info("Both images were equivalent!")
    newImage
  }

  // Return: either None (solution is connected), or Some(blocking clause)
  // needed to block this disconnected solution.
  // FIXME we might want to pre-compute components and use that for
  // optimisations along the way.
  private def connectiveTheory(
      solution: Set[FromLabelTo]
  ): Option[Map[FromLabelTo, Set[FromLabelTo]]] =
    Exploration.measure("parikhImage::connectiveTheory") {
      println(solution.map(fmtTransition(_)))

      val solutionGraph =
        this.dropEdges(this.edges.filter(!solution.contains(_)).to)

      println(solutionGraph.edges.map(fmtTransition(_)))

      val it = solutionGraph.startBFSFrom(initialState)
      val reachedFromStart = it.to[Set]
      val unreached = it.unvisited.to[Set]

      if (unreached.isEmpty) return None

      logger.debug(
        "The following states were unreachable from start " + state2Index(
          initialState
        )
          + ": "
          + unreached
            .map(state2Index(_))
      )

      // Create a new graph with all the reachable nodes merged into one
      val solutionMerged = this.mergeNodes(reachedFromStart)

      println("Original graph:")
      for (edge <- this.edges) {
        println(fmtTransition(edge))
      }

      // println("Merged:")
      // for (edge <- solutionMerged.edges) {
      //   println(fmtTransition(edge))
      // }

      // for (state <- solutionMerged.allNodes) {
      //   println(state2Index(state))

      // }

      // Compute the smallest set of pairs of transition in cycle => one of
      // these transitions must be included for connectivity
      def causeResolution(
          cycle: Set[State]
      ): Seq[(FromLabelTo, Set[FromLabelTo])] = {
        // TODO: compute the min-cut of a homomorphism with the cycle
        // merged into a single node, or, even better, pre-compute a
        // homomorphism with all cycles merged

        logger.debug(s"causeResolution: ${cycle.map(state2Index(_))}")

        // Also merge the cycle into one node
        val cycleSolutionMerged = solutionMerged.flatMergeNodes(cycle)
        import cycleSolutionMerged.equivalentNode

        val connectingEdges =
          cycleSolutionMerged
            .minCut(
              initialState,
              cycle.head
            )
            .flatMap { case (_, realEdges, _) => realEdges }
        assert(!connectingEdges.isEmpty, "Found no connecting edges!")
        logger.info(s"Min-cut is ${connectingEdges.map(fmtTransition(_))}")

        // TODO: this always filters the entire graph; we should pre-compute a
        // smaller subset of just transitions in the cycles we have to filter on
        val transitionsInCycle = solution.filter {
          case (from, _, to) =>
            (cycle contains from) && (cycle contains to)
        }
        transitionsInCycle.map(t => (t, connectingEdges)).toVector
      }

      val cycles = solutionGraph.subgraph(unreached).simpleCycles
      //println("Identified cycles: " + cycles.map(x => x.map(state2Index(_))))

      val implications = cycles
        .flatMap(causeResolution(_))
        .toMap

      Some(implications)

    }

  def parikhImageNew: Formula = Exploration.measure("parikhImageNew") {
    import TerForConvenience._
    // FIXME What does this do?
    implicit val order = TermOrder.EMPTY.extend(registers.map {
      case IConstant(c) => c
    })

    println("# accepting: " + acceptingStates.size)
    acceptingStates.foldRight(Conjunction.FALSE)(
      (finalState, currentSolution) =>
        disjFor(parikhPathToEnd(finalState, currentSolution), currentSolution)
    )
  }

  // FIXME this method is too long
  // FIXME: this method makes a mess of which variables belong to the solver,
  // and which variables are "ours"
  def parikhPathToEnd(finalState: State, blockingConstraint: Formula): Formula =
    Exploration.measure("parikhImagePathToEnd") {
      import TerForConvenience._

      // FIXME use withSolver or whatever it's called
      val solver = SimpleAPI.spawnWithLog // WithAssertions

      for (IConstant(c) <- registers)
        solver.addConstantRaw(c)

      // Each transition gets a constant
      val transitionVarSeq = transitions
        .map(t => (t -> solver.createConstant))
        .toVector
      val transitionVar = transitionVarSeq.toMap

      val registerVarSeq =
        registers.map(r => (r -> solver.createConstant)).toVector
      val registerVar = registerVarSeq.toMap

      implicit val order = solver.order

      val registerInvMap: Map[ConstantTerm, Term] =
        registerVar.map { case (IConstant(d), IConstant(c)) => d -> c }.toMap

      solver.addAssertion(
        Conjunction.negate(
          ConstantSubst(registerInvMap, order)(blockingConstraint),
          order
        )
      )

      // Transition variables are positive
      solver addAssertion (transitionVar.values.toSeq >= 0)

      def registerEqTransitions(xi: (ITerm, Int)) = {
        val (x, registerIdx) = xi
        IExpression.sum(
          for ((t, y) <- transitionVarSeq;
               coeff = etaMap(t)(registerIdx);
               if coeff != 0)
            yield (coeff * y)
        ) === x
      }

      val registerEqs =
        IExpression.and(
          registerVarSeq
            .map(_._2)
            .zipWithIndex
            .map(registerEqTransitions(_))
        )

      println("register equations: " + registerEqs)

      // x_r = sum(r in transition y)(|r| * y)
      solver.addAssertion(registerEqs)

      def transitionTerms(prod: FromLabelTo): List[(State, ap.parser.ITerm)] = {
        val y = transitionVar(prod)

        val (from, _, to) = prod

        // Self-loop: empty list
        if (from == to) return List()

        List((to, -1 * y), (from, y))
      }

      val flowEquations = new ArrayBuffer[IFormula]

      def postAsFlowEquation(
          stateTerms: List[(State, ap.parser.ITerm)]
      ): Unit = {
        val (state, _) = stateTerms.head
        val stateFlowEq = stateTerms.unzip._2.reduce(_ + _)
        val extraTerm = (if (state == finalState) 1 else 0) - (if (state == initialState)
                                                                 1
                                                               else 0)
        val finalEquation = stateFlowEq +++ extraTerm === 0
        solver.addAssertion(finalEquation)
        flowEquations += finalEquation
      }

      def selectEdgesFrom(
          flowSolution: ap.SimpleAPI.PartialModel
      ): Set[FromLabelTo] =
        Exploration.measure("parikhImage::selectEdgesFrom") {

          def transitionInSolution(
              transitionAndY: (FromLabelTo, ap.parser.ITerm)
          ): Boolean = {
            val (_, y) = transitionAndY

            (flowSolution eval y) map (_.intValue) match {
              case None             => false
              case Some(x) if x > 0 => true
              case _                => false
            }
          }

          transitionVar
            .filter(transitionInSolution)
            .keys
            .toSet
        }

      def edgesToConjunctionI(selectedEdges: Set[FromLabelTo]): IFormula = {
        import IExpression._
        and(
          transitionVar.iterator
            .map {
              case (t, c) =>
                if (selectedEdges contains t) (c > 0) else (c === 0)
            }
        )
      }

      def implicationsToBlockingClause(
          implications: Map[FromLabelTo, Set[FromLabelTo]]
      ): ap.parser.IFormula = {

        println("CONNECTED IMPLICATIONS")
        for ((included, correction) <- implications) {
          println(
            fmtTransition(included) +
              " ==> " +
              "(" + correction.map(fmtTransition(_)).mkString(" || ") + ")"
          )
        }
        println("Which means... (in variables)")

        for ((included, correction) <- implications) {
          println(
            s"${transitionVar(included)} > 0" +
              " ==> " +
              "(" + correction
              .map(v => s"${transitionVar(v)} > 0")
              .mkString(" || ") + ")"
          )
        }
        println("END IMPLICATIONS")

        implications
          .map {
            case (t, connectors) =>
              (transitionVar(t) > 0) ===>
                IExpression.or(connectors.map(transitionVar(_) > 0))
          }
          .reduce(_ &&& _)
      }

      transitions
        .map(transitionTerms)
        .flatten
        .toList
        .groupBy(_._1)
        .values
        .foreach(postAsFlowEquation)

      // These are the clauses of the Parikh Image
      val image: ArrayBuffer[Formula] = ArrayBuffer()

      // start a second solver for QE
      val qeSolver = SimpleAPI.spawn // WithAssertions

      qeSolver.addConstantsRaw(solver.order sort solver.order.orderedConstants)

      println("" + transitions.size + " transitions")
      println("" + flowEquations.size + " flow equations")

      // FIXME make this a stream-generating method that streams out generalised
      // solutions, and ditch the arraybuffer

      var previousSolution: Option[Any] = None

      while (solver.??? == SimpleAPI.ProverStatus.Sat) {
        val flowSolution = solver.partialModel
        logger.debug("New flow solution: " + flowSolution)
        val selectedEdges = selectEdgesFrom(flowSolution)
        logger.debug("selected edges: " + selectedEdges.map(fmtTransition(_)))
        previousSolution map (
            x =>
              assert(
                x != selectedEdges,
                s"Selected ${selectedEdges.map(fmtTransition(_))} twice"
              )
          )

        previousSolution = Some(selectedEdges)

        val blockedClause = connectiveTheory(selectedEdges) match {
          case Some(implications) => {
            logger.debug("Disconnected!")
            implicationsToBlockingClause(implications)
          }

          case None => {

            val matrix =
              edgesToConjunctionI(selectedEdges) &&&
                registerEqs &&&
                IExpression.and(flowEquations)

            val elimSol =
              qeSolver.projectEx(matrix, registerVar.values)

            image += solver.asConjunction(elimSol)
            ~elimSol
          }
        }

        logger.debug("Blocking clause:" + blockedClause)
        solver.addAssertion(blockedClause)
      }

      solver.shutDown
      qeSolver.shutDown

      val registerMap: Map[ConstantTerm, Term] =
        registerVar.map { case (IConstant(c), IConstant(d)) => d -> c }.toMap

      logger.debug(
        "Generated path expression: " + ConstantSubst(registerMap, order)(
          disjFor(image)
        )
      )
      ConstantSubst(registerMap, order)(disjFor(image))
    }

  def parikhImageOld: Formula =
    Exploration.measure("parikhImageOld") {
      import TerForConvenience._

      val constantSeq = registers.map { case IConstant(c) => c }
      implicit val order = TermOrder.EMPTY.extend(constantSeq)

      // val a = registers.map(InputAbsy2Internal(_,TermOrder.EMPTY)).toSeq

      lazy val preStates = {
        val preStates =
          Array.fill(stateSeq.size)(new ArrayBuffer[(Int, List[Int])])

        for ((from, label, to) <- transitions) {
          val vector = etaMap((from, label, to))
          preStates(state2Index(to)) += ((state2Index(from), vector))
        }

        preStates
      }
      lazy val transPreStates = {
        val transPreStates = Array.fill(stateSeq.size)(new MBitSet)

        // transPreStates clone from preStates
        for ((array, s2) <- preStates.iterator zip transPreStates.iterator)
          for ((s1, _) <- array)
            s2 += s1

        for ((s, n) <- transPreStates.iterator.zipWithIndex)
          s += n

        var changed = false
        do {
          for (outgoing <- transPreStates) {
            val oldSize = outgoing.size

            for (target <- outgoing)
              // FIXME: only look at the new targets in next iteration!
              outgoing |= transPreStates(target)

            changed = outgoing.size > oldSize
          }
        } while (changed)

        transPreStates
      }
      val initialStateInd = state2Index(initialState)

      ////////////////////////////////////////////////////////////////////////////

      // disjunction of formulas
      val rawDisjunction = disjFor(
        for (finalState <- acceptingStates)
          yield {
            val finalStateInd = state2Index(finalState)
            val refStates = transPreStates(finalStateInd)

            // FIXME: remove self-loops maybe?
            // [to, Option[from] [labels]]
            val productions: List[(Int, Option[Int], List[Int])] =
              (if (refStates contains initialStateInd)
                 List((initialStateInd, None, List()))
               else List()) ::: // FIXME: why concat?
                (for (state <- refStates.iterator;
                      preState <- preStates(state))
                  yield (state, Some(preState._1), preState._2)).toList

            val prodVars = productions.view.zipWithIndex.map {
              case (_, i) => v(i)
            }
            val zVars = refStates
              .zip(Stream from prodVars.size)
              .map {
                case (state, index) =>
                  state -> v(index)
              }
              .toMap

            // Generate 0 - 2 variable -> coefficient * term mappings from a
            // transition , eg.
            // A TRANS TO would give
            //   [A -> 1 * Y_A->B,
            //    B -> -1 * Y_A->B]
            def stateTermsFromTransition(
                t: ((Int, Option[Int], Any), VariableTerm)
            ): List[(Int, (IdealInt, VariableTerm))] =
              t match {
                // Ignore self-loops:
                case ((to, Some(from), _), _) if from == to => List()
                case ((to, None, _), v)                     => List((to, (IdealInt.MINUS_ONE, v)))
                case ((to, Some(from), _), v) =>
                  List((to, (IdealInt.MINUS_ONE, v)), (from, (IdealInt.ONE, v)))
              }

            // Translate the weird output of groupBy to actual linear
            // combinations using the coefficients generated by
            // stateTermsFromTransition. For the final state, add +1 to the
            // terms as per the algorithm.
            def termsToLinearEq(
                st: ((Int, List[(Int, (IdealInt, VariableTerm))]))
            ): LinearCombination = {
              val (state, state_terms) = st
              val terms = state_terms.map(_._2)

              if (state == finalStateInd)
                LinearCombination((IdealInt.ONE, OneTerm) :: terms, order)
              else LinearCombination(terms, order)
            }

            // [((to, from, registers), Z_prod)]
            val prodsWithVars = productions.zip(prodVars).toList

            // equations relating the production counters
            // consistent
            // Transition equations (for non-terminals)
            // [Eq(0/1  +/- Y_transition_1, ..., +/- Y_transition_n),
            // ... ] (+ for from, - for to), one per terminal involved
            // NOTE: This is backwards compared to the paper: 1 on final, reversed sign on from/to
            val prodEqs = prodsWithVars
              .map(stateTermsFromTransition)
              .flatten
              .groupBy(_._1) // group by state
              .map(termsToLinearEq) // translate to each state's equation

            // registers

            // Create the terms for the register equation:
            def makeRegisterTerms(ri: (ITerm, Int)): LinearCombination = {
              val (r, i) = ri
              val prodTerms = prodsWithVars
                .filter { case ((_, from, regs), _) => from != None }
                .map {
                  case ((_, _, regs), prodVar) => (IdealInt(regs(i)), prodVar)
                }

              LinearCombination(
                (IdealInt.MINUS_ONE, InputAbsy2Internal(r, order)) :: prodTerms,
                order
              )
            }

            // for each register, generate a linear combination of -1 * r +
            // [y_A->B * s(r)], where s(r) for each register r, where s(r) is
            // the...state of register r at state s.
            val rEqs = registers.zipWithIndex
              .map(makeRegisterTerms)

            val entryZEq = zVars(finalStateInd) - 1

            val allEqs = eqZ(Iterator(entryZEq) ++ prodEqs ++ rEqs)

            val prodNonNeg = prodVars >= 0

            // Production implications: either we didn't use a production, or
            // its corresponding target is greater than zero.
            val prodImps = prodsWithVars
              .filter { case ((to, _, _), _) => to != finalStateInd }
              .map {
                case ((to, _, _), prodVar) => (prodVar === 0) | zVars(to) > 0
              }

            val connective = refStates
              .filter(finalStateInd.!=)
              .map(
                state =>
                  disjFor(
                    (zVars(state) === 0) ::
                      prodsWithVars
                        .filter {
                          case ((_, from, _), _) => from contains state
                        }
                        .map {
                          case ((to, _, _), prodVar) =>
                            conj(
                              zVars(state) === zVars(to) + 1,
                              geqZ(List(prodVar - 1, zVars(to) - 1))
                            )
                        }
                  )
              )

            val matrix =
              conj(Iterator(allEqs, prodNonNeg) ++ prodImps ++ connective)
            val rawConstraint =
              exists(prodVars.size + zVars.size, matrix)

            /*            val constraint =
              ap.util.Timeout.withTimeoutMillis(1000) {
                // best-effort attempt to get a quantifier-free version of the
                // length abstraction
                PresburgerTools.elimQuantifiersWithPreds(rawConstraint)
              } {
                ReduceWithConjunction(Conjunction.TRUE, order)(rawConstraint)
              }*/

            rawConstraint
          }
      )

      if (rawDisjunction.variables.isEmpty) {
        rawDisjunction
      } else {
        val maxVar =
          (for (VariableTerm(n) <- rawDisjunction.variables) yield n).max
        exists(maxVar + 1, rawDisjunction)
      }
    }

  /**
    * addEtaMap, vector.length must equal to registers.length
    */
  def addEtaMap(transition: (State, TLabel, State), vector: List[Int]): Unit = {
    etaMap += (transition -> vector)
  }

  /**
    * addEtaMaps, input is a hashmap
    */
  def addEtaMaps(map: MHashMap[(State, TLabel, State), List[Int]]): Unit = {
    etaMap ++= map
  }

  /**
    * addEtaMapDefault, the default vector is considered to be 0
    */
  def addEtaMapDefault(transition: (State, TLabel, State)): Unit = {
    val vector = List.fill(registers.length)(0)
    addEtaMap(transition, vector)
  }

  /**
    * addEtaMapsDefault
    */
  def addEtaMapsDefault(): Unit = {
    for ((s1, l, s2) <- this.transitions) {
      addEtaMapDefault((s1, l, s2))
    }
  }
  val debugTransitions = {
    (for ((s1, l, s2) <- this.transitions) yield (s1, l, s2)).toList
  }

  /**
    * register op:
    */
  def addNewRegister(num: Int): Unit = {
    for (i <- 1 to num)
      registers += AllocRegisterTerm()
  }
  def addRegisters(rs: ArrayBuffer[ITerm]): Unit = {
    registers ++= rs
  }
  def setRegisters(rs: ArrayBuffer[ITerm]): Unit = {
    registers.clear()
    registers ++= rs
  }
  def setRegisters(rs: List[ITerm]): Unit = {
    registers.clear()
    registers ++= rs
  }

  /**
    * cloneRegisters : clone register, use the different token
    */
  def cloneRegisters(): ArrayBuffer[ITerm] = {
    val res: ArrayBuffer[ITerm] = ArrayBuffer()
    for (i <- registers) {
      res += AllocRegisterTerm()
    }
    res
  }

  // print this aut
//  def printAut() : Unit = {
//    val out = new PrintWriter(new FileWriter("tmp.txt", true))
//    val statesIndex = states.zipWithIndex.toMap
//    out.println("#automata:")
//    out.println("#states: "+states.size)
//    out.println("#init: "+ statesIndex(initialState))
//    out.print("#final: ")
//    acceptingStates.foreach{case state => print(statesIndex(state) + ",")}
//    out.println()
//    out.println("#transitons: ")
//    etaMap.foreach{case ((from, (charmin,charmax), to),vector) =>
//      out.println(statesIndex(from)+";"+statesIndex(to)+";"+charmin.toInt+";"+charmax.toInt+";"+vector)}
//    out.print("#register: ")
//    registers.foreach{case r => out.print(r + ",")}
//    out.println()
//    out.close()
//  }

  // hu zi add ------------------------------------------------------------------------------------------------------

  /**
    * Union
    */
  def |(that: Automaton): Automaton =
    new BricsAutomaton(
      BasicOperations.union(this.underlying, toBAutomaton(that))
    )

  /**
    * Intersection
    */
  def &(that: Automaton): Automaton = {
    val productAut =
      BasicOperations.intersection(this.underlying, toBAutomaton(that))
    productAut.minimize()
    new BricsAutomaton(productAut)
  }

  /**
    * Complementation
    */
  def unary_! : Automaton =
    new BricsAutomaton(BasicOperations.complement(this.underlying))

  /**
    * Check whether this automaton describes the empty language.
    */
  def isEmpty: Boolean =
    underlying.isEmpty

  /**
    * Check whether the automaton accepts a given word.
    */
  def apply(word: Seq[Int]): Boolean =
    BasicOperations.run(
      this.underlying,
      SeqCharSequence(for (c <- word.toIndexedSeq) yield c.toChar).toString
    )

  /**
    * Iterate over automaton states, return in deterministic order
    */
  lazy val states: Iterable[State] = {
    // do this the hard way to give a deterministic ordering
    val worklist = new MStack[State]
    val seenstates = new MLinkedHashSet[State]

    worklist.push(initialState)
    seenstates.add(initialState)

    while (!worklist.isEmpty) {
      val s = worklist.pop

      for ((to, _) <- outgoingTransitions(s)) {
        if (!seenstates.contains(to)) {
          worklist.push(to)
          seenstates += to
        }
      }
    }

    seenstates
  }

  /**
    * The unique initial state
    */
  lazy val initialState: State = underlying.getInitialState

  /**
    * Given a state, iterate over all outgoing transitions, try to be
    * deterministic
    */
  def outgoingTransitions(from: State): Iterator[(State, TLabel)] = {
    val dests = new MHashMap[TLabel, MSet[State]] with MMultiMap[TLabel, State]

    for (t <- from.getTransitions)
      dests.addBinding((t.getMin, t.getMax), t.getDest)

    val outgoing = new MLinkedHashSet[(State, TLabel)]

    for (lbl <- dests.keys.toList.sorted) {
      for (s <- dests(lbl)) {
        outgoing += ((s, lbl))
      }
    }

    outgoing.iterator
  }

  /**
    * The set of accepting states
    */
  lazy val acceptingStates: Set[State] =
    (for (s <- states; if s.isAccept) yield s).toSet

  lazy val labelEnumerator =
    new BricsTLabelEnumerator(for ((_, lbl, _) <- transitions) yield lbl)

  /**
    * Get any word accepted by this automaton, or <code>None</code>
    * if the language is empty
    */
  def getAcceptedWord: Option[Seq[Int]] =
    (this.underlying getShortestExample true) match {
      case null => None
      case str  => Some(for (c <- str) yield c.toInt)
    }

  /**
    * Simplify this automaton. Currently, this might not necessarily result
    * in an automaton with a minimal number of states, however.
    */
  def minimize: BricsAutomaton = {
    val stateAr = states.toArray
    val N = stateAr.size

    val labelSet = for (s <- stateAr) yield {
      (for ((t, l) <- outgoingTransitions(s))
        yield (l, etaMap((s, l, t)))).toSet
    }
    val stateIndex = stateAr.iterator.zipWithIndex.toMap

    // Initial relation between states
    val eqvStates = Array.tabulate(N) { n1 =>
      {
        val s1 = stateAr(n1)
        BitSet(
          (for (n2 <- 0 until n1;
                s2 = stateAr(n2);
                if isAccept(s1) == isAccept(s2);
                if labelSet(n1) == labelSet(n2)) yield n2): _*
        )
      }
    }

    if (eqvStates forall (_.isEmpty))
      return this

    def areEqv(n1: Int, n2: Int) =
      if (n1 < n2)
        eqvStates(n2)(n1)
      else if (n2 < n1)
        eqvStates(n1)(n2)
      else
        true

    def transSubsumes(n1: Int, n2: Int) = {
      val s1 = stateAr(n1)
      val s2 = stateAr(n2)
      outgoingTransitions(s1) forall {
        case (t1, l1) => {
          val eta1 = etaMap((s1, l1, t1))
          val t1Ind = stateIndex(t1)
          outgoingTransitions(s2) exists {
            case (t2, l2) =>
              l1 == l2 &&
                eta1 == etaMap((s2, l2, t2)) &&
                areEqv(t1Ind, stateIndex(t2))
          }
        }
      }
    }

    // fixed-point loop to refine the relation between states
    var cont = true
    while (cont) {
      cont = false
      for (n1 <- 0 until N) {
        val oldEqv = eqvStates(n1)
        if (!oldEqv.isEmpty) {
          val newEqv =
            for (n2 <- oldEqv;
                 if transSubsumes(n1, n2) && transSubsumes(n2, n1))
              yield n2
          if (oldEqv != newEqv) {
            cont = true
            eqvStates(n1) = newEqv
          }
        }
      }
    }

    if (eqvStates forall (_.isEmpty))
      return this

    // construct a new, reduced automaton
    val builder = getBuilder

    val newStates =
      (for (n <- 0 until N; if eqvStates(n).isEmpty)
        yield (n -> builder.getNewState)).toMap

    val old2New =
      (for (n1 <- 0 until N) yield {
        val s1 = stateAr(n1)
        val eqv = eqvStates(n1)
        s1 -> newStates(if (eqv.isEmpty) n1 else eqv.min)
      }).toMap

    builder setInitialState old2New(initialState)

    for ((s, n) <- stateAr.iterator.zipWithIndex;
         if eqvStates(n).isEmpty;
         (t, l) <- outgoingTransitions(s))
      builder.addTransition(old2New(s), l, old2New(t), etaMap((s, l, t)))

    for (s <- stateAr)
      builder.setAccept(old2New(s), isAccept(s))

    val res = builder.getAutomaton
    res.addEtaMaps(builder.etaMap)
    res setRegisters this.registers
    res
  }

  /**
    * Eliminate labels (character ranges) from this automaton; labels
    * for transitions with distinct eta labels will still be kept
    * distinct as well, to avoid transitions being merged that should
    * be kept
    */
  def makeLabelsUniform: BricsAutomaton = {
    val etaIndex = new MHashMap[List[Int], Int]

    val builder = getBuilder
    val old2New =
      (for (s <- states) yield (s -> builder.getNewState)).toMap

    builder setInitialState old2New(initialState)

    for (s <- states)
      builder.setAccept(old2New(s), isAccept(s))

    for (s <- states;
         (t, l) <- outgoingTransitions(s);
         eta = etaMap((s, l, t))) {
      val index = etaIndex.getOrElseUpdate(eta, etaIndex.size).toChar
      builder.addTransition(old2New(s), (index, index), old2New(t), eta)
    }

    val res = builder.getAutomaton
    res.addEtaMaps(builder.etaMap)
    res setRegisters this.registers
    res
  }

  def isAccept(s: State): Boolean = s.isAccept

  def toDetailedString: String = underlying.toString

  def getBuilder: BricsAutomatonBuilder = new BricsAutomatonBuilder

  def getTransducerBuilder: BricsTransducerBuilder = BricsTransducer.getBuilder

  /**
    *  Graph trait implementation
    * */
  def allNodes() = states.to
  def edges() = transitions.to
  def transitionsFrom(node: State) =
    outgoingTransitions(node).map(t => (node, t._2, t._1)).toSeq
  def subgraph(selectedNodes: Set[State]): RichGraph[State, TLabel] = ???
  def dropEdges(edgesToDrop: Set[(State, TLabel, State)]) = {
    val selectedEdges: Set[(State, TLabel, State)] = this
      .edges()
      .toSet &~ edgesToDrop
    new MapGraph(selectedEdges.toSeq)
  }

  def addEdges(edgesToAdd: Iterable[(State, TLabel, State)]) = {
    val selectedEdges: Set[(State, TLabel, State)] = this
      .edges()
      .toSet ++ edgesToAdd
    new MapGraph(selectedEdges.toSeq)
  }

}

/**
  * For constructing manually (immutable) BricsAutomaton objects
  */
class BricsAutomatonBuilder
    extends AtomicStateAutomatonBuilder[
      BricsAutomaton#State,
      BricsAutomaton#TLabel
    ] {
  val LabelOps: TLabelOps[BricsAutomaton#TLabel] = BricsTLabelOps

  var minimize = true

  val baut: BAutomaton = {
    val baut = new BAutomaton
    baut.setDeterministic(false)
    baut
  }

  val etaMap = new MHashMap[
    (BricsAutomaton#State, BricsAutomaton#TLabel, BricsAutomaton#State),
    List[Int]
  ]

  /**
    * The initial state of the automaton being built
    */
  def initialState: BricsAutomaton#State = baut.getInitialState

  /**
    * By default one can assume built automata are minimised before the
    * are returned.  Use this to enable or disable it
    */
  def setMinimize(minimize: Boolean): Unit = { this.minimize = minimize }

  /**
    * Create a fresh state that can be used in the automaton
    */
  def getNewState: BricsAutomaton#State = new BState()

  /**
    * Set the initial state
    */
  def setInitialState(q: BricsAutomaton#State): Unit =
    baut.setInitialState(q)

  /**
    * Add a new transition q1 --label--> q2
    */
  def addTransition(
      q1: BricsAutomaton#State,
      label: BricsAutomaton#TLabel,
      q2: BricsAutomaton#State
  ): Unit = {
    if (LabelOps.isNonEmptyLabel(label)) {
      val (min, max) = label
      q1.addTransition(new Transition(min, max, q2))
    }
  }

  // huzi add-----------------------------------------
  def addTransition(
      q1: BricsAutomaton#State,
      label: BricsAutomaton#TLabel,
      q2: BricsAutomaton#State,
      vector: List[Int]
  ): Unit = {
    if (LabelOps.isNonEmptyLabel(label)) {
      val (min, max) = label
      q1.addTransition(new Transition(min, max, q2))
      etaMap += ((q1, (min, max), q2) -> vector)
    }
  }

  def outgoingTransitions(
      q: BricsAutomaton#State
  ): Iterator[(BricsAutomaton#State, BricsAutomaton#TLabel)] =
    for (t <- q.getTransitions.iterator)
      yield (t.getDest, (t.getMin, t.getMax))

  def setAccept(q: BricsAutomaton#State, isAccepting: Boolean): Unit =
    q.setAccept(isAccepting)

  def isAccept(q: BricsAutomaton#State): Boolean = q.isAccept

  /**
    * Remove states and transitions from which no accepting states can be
    * reached
    */
  def removeBackwardsUnreachableStates(): Unit = {
    val reachable = new MHashSet[BricsAutomaton#State]
    val allStates = states

    for (s <- allStates)
      if (s.isAccept)
        reachable += s

    var changed = true
    while (changed) {
      changed = false
      for (s <- allStates)
        if (!(reachable contains s))
          for ((next, _) <- outgoingTransitions(s))
            if (reachable contains next) {
              reachable += s
              changed = true
            }
    }

    // cut transitions to all unreachable states
    for (s <- allStates)
      if (reachable contains s) {
        val transitions = s.getTransitions

        for (t <- transitions.toList)
          if (!(reachable contains t.getDest))
            transitions remove t
      }
  }

  /**
    * Iterate over automaton states, return in deterministic order
    */
  private def states: Iterable[BricsAutomaton#State] = {
    // do this the hard way to give a deterministic ordering
    val worklist = new MStack[BricsAutomaton#State]
    val seenstates = new MLinkedHashSet[BricsAutomaton#State]

    worklist.push(initialState)
    seenstates.add(initialState)

    while (!worklist.isEmpty) {
      val s = worklist.pop

      for ((to, _) <- outgoingTransitions(s)) {
        if (!seenstates.contains(to)) {
          worklist.push(to)
          seenstates += to
        }
      }
    }

    seenstates
  }

  /**
    * Returns built automaton.  Can only be used once after which the
    * automaton cannot change
    */
  def getAutomaton: BricsAutomaton = {
    new BricsAutomaton(baut)
  }
}

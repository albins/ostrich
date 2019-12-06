/*
 * This file is part of Sloth, an SMT solver for strings.
 * Copyright (C) 2017  Philipp Ruemmer, Petr Janku
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

import ap.terfor.Term
import ap.terfor.preds.{Predicate, Atom, PredConj}

import dk.brics.automaton.{BasicAutomata, BasicOperations, RegExp, Automaton}

import scala.collection.JavaConverters._
import scala.collection.mutable.ArrayBuffer

class Regex2AFA(atoms: PredConj) {
  import StringTheory._
  private val p = functionPredicateMap

  private def numToUnicode(num: Int): String =
    new String(Character.toChars(num))

  // build regex string in brics format for term c
  def buildRegex(c: Term): String =
    (for (a <- atoms positiveLitsWithPred p(rexEmpty); if (a(0) == c))
      yield "#").headOption orElse
      (for (a <- atoms positiveLitsWithPred p(rexEps); if (a(0) == c))
        yield "()").headOption orElse
      (for (a <- atoms positiveLitsWithPred p(rexSigma); if (a(0) == c))
        yield ".").headOption orElse
      (for (a <- atoms positiveLitsWithPred p(rexChar); if (a(1) == c))
        yield {
          assert(a(0).isConstant)
          "\\" + numToUnicode(a(0).constant.intValueSafe)
        }).headOption orElse
      (for (a <- atoms positiveLitsWithPred p(rexRange); if (a(2) == c))
        yield {
          assert(a(0).isConstant)
          assert(a(1).isConstant)
          "[\\" + numToUnicode(a(0).constant.intValueSafe) + "-" +
            "\\" + numToUnicode(a(1).constant.intValueSafe) + "]"
        }).headOption orElse
      (for (a <- atoms positiveLitsWithPred p(rexCat); if (a(2) == c))
        yield (buildRegex(a(0)) + buildRegex(a(1)))).headOption orElse
      (for (a <- atoms positiveLitsWithPred p(rexUnion); if (a(2) == c))
        yield ("(" + buildRegex(a(0)) + "|" + buildRegex(a(1)) + ")")).headOption orElse
      (for (a <- atoms positiveLitsWithPred p(rexStar); if (a(1) == c))
        yield ("(" + buildRegex(a(0)) + ")*")).headOption orElse
      (for (a <- atoms positiveLitsWithPred p(rexNeg); if (a(1) == c))
        yield ("~" + buildRegex(a(0)))).headOption getOrElse {
      assert(false)
      null
    }

  //////////////////////////////////////////////////////////////////////////////
  // Reconstruct strings from wordEps, wordChar, wordCat

  def buildStrings(c: Term): Iterator[List[Either[Int, Term]]] = {
    val definitions =
      (for (a <- (atoms positiveLitsWithPred p(wordEps)).iterator;
            if (a(0) == c))
        yield List()) ++
        (for (a <- (atoms positiveLitsWithPred p(wordChar)).iterator;
              if (a(0).isConstant && a(1) == c))
          yield {
            List(Left(a(0).constant.intValueSafe))
          }) ++
        (for (a <- (atoms positiveLitsWithPred p(wordCat)).iterator;
              if (a(2) == c);
              left <- buildStrings(a(0));
              right <- buildStrings(a(1)))
          yield (left ::: right))
    if (definitions.hasNext)
      definitions
    else
      Iterator single List(Right(c))
  }

  def buildBricsAut(c: Term): Automaton =
    new RegExp(buildRegex(c)).toAutomaton

}

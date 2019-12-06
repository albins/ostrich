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

import scala.collection.mutable.{
  HashSet => MHashSet,
  ArrayStack,
  Stack => MStack,
  HashMap => MHashMap,
  MultiMap,
  ArrayBuffer,
  Set => MSet
}
// import dk.brics.automaton.{Transition, State}

/**
  * Collection of useful functions for automata
  */
object AutomataUtils {

  /**
    * The maximum number of automata to product simultaneously
    */
  val MaxSimultaneousProduct = 5

  /**
    * Check whether there is some word accepted by all of the given automata.
    * The automata are required to all have the same label type (though this is
    * not checked statically)
    */
  def areConsistentAtomicAutomata(auts: Seq[AtomicStateAutomaton]): Boolean = {
    val autsList = auts.toList
    val visitedStates = new MHashSet[List[Any]]
    val todo = new ArrayStack[List[Any]]

    def isAccepting(states: List[Any]): Boolean =
      (auts.iterator zip states.iterator) forall {
        case (aut, state) =>
          aut.acceptingStates contains state.asInstanceOf[aut.State]
      }

    def enumNext(
        auts: List[AtomicStateAutomaton],
        states: List[Any],
        intersectedLabels: Any
    ): Iterator[List[Any]] =
      auts match {
        case List() =>
          Iterator(List())
        case aut :: otherAuts => {
          val state :: otherStates = states
          for ((to, label) <- aut.outgoingTransitions(
                 state.asInstanceOf[aut.State]
               );
               newILabel <- aut.LabelOps
                 .intersectLabels(
                   intersectedLabels.asInstanceOf[aut.TLabel],
                   label
                 )
                 .toSeq;
               tailNext <- enumNext(otherAuts, otherStates, newILabel))
            yield (to :: tailNext)
        }
      }

    val initial = (autsList map (_.initialState))

    if (isAccepting(initial))
      return true

    visitedStates += initial
    todo push initial

    while (!todo.isEmpty) {
      val next = todo.pop
      for (reached <- enumNext(autsList, next, auts.head.LabelOps.sigmaLabel))
        if (visitedStates.add(reached)) {
          if (isAccepting(reached))
            return true
          todo push reached
        }
    }

    false
  }

  /**
    * Check whether there is some word accepted by all of the given automata.
    */
  def areConsistentAutomata(auts: Seq[Automaton]): Boolean =
    if (auts.isEmpty) {
      true
    } else if (auts forall (_.isInstanceOf[AtomicStateAutomaton])) {
      areConsistentAtomicAutomata(
        auts map (_.asInstanceOf[AtomicStateAutomaton])
      )
    } else {
      !(auts reduceLeft (_ & _)).isEmpty
    }

  /**
    * Check whether there is some word accepted by all of the given automata.
    * If the intersection is empty, return an unsatisfiable core. The method
    * makes the assumption that <code>oldAuts</code> are consistent, but the
    * status of the combination with <code>newAut</code> is unknown.
    */
  def findUnsatCore(
      oldAuts: Seq[Automaton],
      //huzi add :
      productAut: Automaton,
      //huzi add :
      newAut: Automaton
  ): Option[Seq[Automaton]] = {

    val consideredAuts = new ArrayBuffer[Automaton]
    consideredAuts ++= oldAuts
    consideredAuts += newAut

    // // add automata until we encounter a conflict
    // var cont = areConsistentAutomata(consideredAuts)
    // val oldAutsIt = oldAuts.iterator
    // while (cont && oldAutsIt.hasNext) {
    //   consideredAuts += oldAutsIt.next
//       cont = areConsistentAutomata(consideredAuts)
    // }

    // if (cont)
    //   return None

    //    val prod = productAut & newAut
    //    val debug = prod
    val consist = !(productAut & newAut).isEmpty
    if (consist)
      return None
    // remove automata to get a small core
    for (i <- (consideredAuts.size - 2) to 1 by -1) {
      val removedAut = consideredAuts remove i
      if (areConsistentAutomata(consideredAuts))
        consideredAuts.insert(i, removedAut)
    }
    //    Some(oldAuts :+ newAut)
    Some(consideredAuts)

  }

  /**
    * Check whether there is some word of length <code>len</code> accepted
    * by all of the given automata.
    * The automata are required to all have the same label type (though this is
    * not checked statically)
    */
  def findAcceptedWordAtomic(
      auts: Seq[AtomicStateAutomaton],
      len: Int
  ): Option[Seq[Int]] = {
    val autsList = auts.toList
    val headAut = autsList.head
    val visitedStates = new MHashSet[(List[Any], Int)]
    val todo = new ArrayStack[(List[Any], List[Int])]

    def isAccepting(states: List[Any]): Boolean =
      (auts.iterator zip states.iterator) forall {
        case (aut, state) =>
          aut.acceptingStates contains state.asInstanceOf[aut.State]
      }

    def enumNext(
        auts: List[AtomicStateAutomaton],
        states: List[Any],
        intersectedLabels: Any
    ): Iterator[(List[Any], Int)] =
      auts match {
        case List() =>
          Iterator(
            (
              List(),
              headAut.LabelOps
                .enumLetters(intersectedLabels.asInstanceOf[headAut.TLabel])
                .next
            )
          )
        case aut :: otherAuts => {
          val state :: otherStates = states
          for ((to, label) <- aut.outgoingTransitions(
                 state.asInstanceOf[aut.State]
               );
               newILabel <- aut.LabelOps
                 .intersectLabels(
                   intersectedLabels.asInstanceOf[aut.TLabel],
                   label
                 )
                 .toSeq;
               (tailNext, let) <- enumNext(otherAuts, otherStates, newILabel))
            yield (to :: tailNext, let)
        }
      }

    val initial = (autsList map (_.initialState))

    if (isAccepting(initial) && len == 0)
      return Some(List())

    visitedStates += ((initial, 0))
    todo push ((initial, List()))

    while (!todo.isEmpty) {
      val (next, w) = todo.pop
      val wSize = w.size
      for ((reached, let) <- enumNext(
             autsList,
             next,
             auts.head.LabelOps.sigmaLabel
           ))
        if (visitedStates.add((reached, wSize + 1))) {
          val newW = let :: w
          if (isAccepting(reached) && wSize + 1 == len)
            return Some(newW.reverse)
          if (wSize + 1 < len)
            todo push (reached, newW)
        }
    }

    None
  }

  /**
    * Check whether there is some word of length <code>len</code> accepted
    * by all of the given automata.
    */
  def findAcceptedWord(auts: Seq[Automaton], len: Int): Option[Seq[Int]] =
    findAcceptedWordAtomic(
      for (aut <- auts)
        yield aut.asInstanceOf[AtomicStateAutomaton],
      len
    )

  /**
    * Product of a number of given automata.  Returns
    * new automaton.  Returns map from new states of result to (q0, [q1,
    * ..., qn]) giving states of this and auts respectively
    *
    * The minimize argument enable minimization of the product automaton,
    * which should only be used if the returned maps are not used.
    */
  def productWithMap(
      auts: Seq[AtomicStateAutomaton],
      minimize: Boolean = false
  ): (AtomicStateAutomaton, Map[Any, Seq[Any]]) = {
    // 空Map[Any, Seq[Any]]
    val idMap = Map[Any, Seq[Any]]().withDefault(s => Seq(s))
    productWithMaps(auts.map((_, idMap)), minimize)
  }

  /**
    * Takes the product of the list of automata and returns mapping from
    * states of the new automaton to tuples of the original.  auts may
    * already be products and come with a similar map, these are composed
    * for the result map
    *
    * The minimize argument enable minimization of the product automaton,
    * which should only be used if the returned maps are not used.
    */
  private def productWithMaps(
      auts: Seq[(AtomicStateAutomaton, Map[Any, Seq[Any]])],
      minimize: Boolean = false
  ): (AtomicStateAutomaton, Map[Any, Seq[Any]]) = {

    if (auts.size == 0)
      return (BricsAutomaton.makeAnyString, Map.empty[Any, Seq[Any]])

    if (auts.size == 1)
      return auts.head

    val firstSlice = auts
      .grouped(MaxSimultaneousProduct)
      .map(fullProductWithMaps(_, minimize))
      .toSeq

    if (firstSlice.size == 1)
      return firstSlice(0)
    else
      return productWithMaps(firstSlice, minimize)
  }

  /**
    * Takes the product of the list of automata and returns mapping from
    * states of the new automaton to tuples of the original.  auts may
    * already be products and come with a similar map, these are composed
    * for the result map
    * The minimize argument enable minimization of the product automaton,
    * which should only be used if the returned maps are not used.
    */
  private def fullProductWithMaps(
      auts: Seq[(AtomicStateAutomaton, Map[Any, Seq[Any]])],
      minimize: Boolean = false
  ): (AtomicStateAutomaton, Map[Any, Seq[Any]]) = {

    val (autsSeq, mapsSeq) = auts.unzip

    // get image of states under maps in mapsSeq
    // or just return ss if minimize is true
    def mapsImage(ss: Seq[Any]): List[Any] = {
      if (minimize)
        ss.toList
      else
        ss.iterator
          .zip(mapsSeq.iterator)
          .flatMap({ case (s, sMap) => sMap(s) })
          .toList
    }

    val head = autsSeq.head
    val builder = head.getBuilder
    builder.setMinimize(minimize)
    val initState = builder.initialState
    // from new states to list of old (composed with input maps)
    val sMap = new MHashMap[head.State, List[Any]]
    // from list of states of argument automata (not composed with maps)
    val sMapRev = new MHashMap[List[Any], head.State]

    val initStates = (autsSeq.map(_.initialState)).toList
    sMap += initState -> mapsImage(initStates)
    sMapRev += initStates -> initState

    val worklist = new MStack[(head.State, List[Any])]
    worklist push ((initState, initStates))

    val seenlist = MHashSet[List[Any]]()
    seenlist += initStates

    builder.setAccept(initState, autsSeq forall { aut =>
      aut.isAccept(aut.initialState)
    })

    var checkCnt = 0

    while (!worklist.isEmpty) {
      val (ps, ss) = worklist.pop()

      // collects transitions from (s, ss)
      // min, max is current range
      // sp and ssp are s' and ss' (ss' is reversed for efficiency)
      // ss are elements of ss from which a transition is yet to be
      // searched
      def addTransitions(
          lbl: head.TLabel,
          ssp: List[Any],
          remAuts: List[AtomicStateAutomaton],
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
              val isAccept = (autsSeq.iterator zip nextState.iterator) forall {
                case (aut, s) => aut.isAccept(s.asInstanceOf[aut.State])
              }
              builder.setAccept(nextPState, isAccept)
              sMap += nextPState -> mapsImage(nextState)
              sMapRev += nextState -> nextPState
              worklist.push((nextPState, nextState))
              seenlist += nextState
            }
            val nextPState = sMapRev(nextState)
            builder.addTransition(ps, lbl, nextPState)
          }
          case _state :: ssTail => {
            val aut :: autsTail = remAuts
            val state = _state.asInstanceOf[aut.State]

            aut.outgoingTransitions(state) foreach {
              case (s, nextLbl) => {
                val newLbl =
                  builder.LabelOps
                    .intersectLabels(lbl, nextLbl.asInstanceOf[head.TLabel])
                for (l <- newLbl)
                  addTransitions(l, s :: ssp, autsTail, ssTail)
              }
            }
          }
        }
      }

      addTransitions(builder.LabelOps.sigmaLabel, List(), autsSeq.toList, ss)
    }

    (builder.getAutomaton, sMap.toMap)
  }

  /**
    * Form product of this automaton with given auts, returns a new
    * automaton
    */
  def product(auts: Seq[AtomicStateAutomaton]): AtomicStateAutomaton =
    productWithMap(auts, true)._1

  /**
    * Replace a-transitions with new a-transitions between pairs of states
    */
  def replaceTransitions[A <: AtomicStateAutomaton](
      aut: A,
      a: Char,
      states: Iterable[(A#State, A#State)]
  ): AtomicStateAutomaton = {
    val builder = aut.getBuilder
    val smap: Map[A#State, aut.State] =
      aut.states.map(s => (s -> builder.getNewState))(collection.breakOut)

    for ((s1, lbl, s2) <- aut.transitions)
      for (newLbl <- aut.LabelOps.subtractLetter(a, lbl))
        builder.addTransition(smap(s1), newLbl, smap(s2))

    val aLbl = aut.LabelOps.singleton(a)
    for ((s1, s2) <- states)
      builder.addTransition(smap(s1), aLbl, smap(s2))

    builder.setInitialState(smap(aut.initialState))
    for (f <- aut.acceptingStates)
      builder.setAccept(smap(f), true)

    val res = builder.getAutomaton
    res
  }

  /**
    * Build automaton accepting reverse language of given automaton
    */
  def reverse(aut: AtomicStateAutomaton): AtomicStateAutomaton = {
    val builder = aut.getBuilder

    val smap: Map[aut.State, aut.State] =
      aut.states.map(s => (s -> builder.getNewState))(collection.breakOut)

    val initState = builder.initialState
    builder.setAccept(smap(aut.initialState), true)

    val autAccept = aut.acceptingStates
    for ((s1, l, s2) <- aut.transitions) {
      if (autAccept contains s2)
        builder.addTransition(initState, l, smap(s1))
      builder.addTransition(smap(s2), l, smap(s1))
    }

    builder.getAutomaton
  }

  // hu zi add ------------------------------------------------------------
  /**
    *  Build BricsAutomaton accepting reverse language of given automaton:
    *
    *  Given an INCRA A = (Σ, Q, I, F, R, δ), the inverse of A, denoted by
    *  A(r), is (Σ, Q, F, I, R, δ') where δ' comprises the tuples
    *   (q', σ, q, η) such that (q, σ, q', η) ∈ δ
    */
  def reverse(aut: BricsAutomaton): BricsAutomaton = {
    val builder = aut.getBuilder
    val etaMap = new MHashMap[(aut.State, aut.TLabel, aut.State), List[Int]]

    val smap: Map[aut.State, aut.State] =
      aut.states.map(s => (s -> builder.getNewState))(collection.breakOut)

    val initState = builder.initialState
    builder.setAccept(smap(aut.initialState), true)

    val autAccept = aut.acceptingStates
    for ((s1, l, s2) <- aut.transitions) {
      val vector = aut.etaMap((s1, l, s2))

      if (autAccept contains s2) {
        builder.addTransition(initState, l, smap(s1), vector)
        //construct (q', σ, q, η) tuple
        //(q', σ, q, η)∈ δ' such that (q, σ, q', η) ∈ δ
        // etaMap += ((initState, l, smap(s1)) -> vector)
      }
      builder.addTransition(smap(s2), l, smap(s1), vector)
      //construct (q', σ, q, η) tuple
      //(q', σ, q, η)∈ δ' such that (q, σ, q', η) ∈ δ
      // etaMap += ((smap(s2), l, smap(s1)) -> vector)
    }

    val res = builder.getAutomaton
    // add (q', σ, q, η) tuple
    res.addEtaMaps(builder.etaMap)
    res.addRegisters(aut.registers)
    res
  }
  // hu zi add ------------------------------------------------------------

  /**
    * Build automaton accepting concat language of given automata
    * aut1 and aut2 must have compatible label types
    */
  def concat(
      aut1: AtomicStateAutomaton,
      aut2: AtomicStateAutomaton
  ): AtomicStateAutomaton = {
    val builder = aut1.getBuilder

    val smap1: Map[aut1.State, aut1.State] =
      aut1.states.map(s => (s -> builder.getNewState))(collection.breakOut)
    val smap2: Map[aut2.State, aut1.State] =
      aut2.states.map(s => (s -> builder.getNewState))(collection.breakOut)

    builder.setInitialState(smap1(aut1.initialState))
    for (sf <- aut2.acceptingStates)
      builder.setAccept(smap2(sf), true)
    if (aut1.isAccept(aut1.initialState))
      for (sf <- aut1.acceptingStates)
        builder.setAccept(smap1(sf), true)

    for ((s1, l, s2) <- aut1.transitions)
      builder.addTransition(smap1(s1), l, smap1(s2))

    for ((s1, l, s2) <- aut2.transitions) {
      val convL = l.asInstanceOf[aut1.TLabel]
      if (s1 == aut2.initialState)
        for (sf <- aut1.acceptingStates)
          builder.addTransition(smap1(sf), convL, smap2(s2))
      builder.addTransition(smap2(s2), convL, smap2(s1))
    }

    builder.getAutomaton
  }

  /**
    * Inserts second automaton into the first replacing transitions over
    * a give character.  I.e. s1 --a--> s2 becomes s1 -->into aut / from
    * final --> s2.
    *
    * Assumes autOuter and autInner have compatible label types
    *
    * This is approximate in that there is only a single copy of the
    * inserted automaton, so ingoing and outgoing transitions are not
    * mapped.
    */
  def nestAutomata(
      autOuter: AtomicStateAutomaton,
      toReplace: Char,
      autInner: AtomicStateAutomaton
  ): AtomicStateAutomaton = {
    val builder = autOuter.getBuilder

    val smapOuter: Map[autOuter.State, autOuter.State] =
      autOuter.states.map(s => (s -> builder.getNewState))(collection.breakOut)
    val smapInner: Map[autInner.State, autOuter.State] =
      autInner.states.map(s => (s -> builder.getNewState))(collection.breakOut)

    val innerInit = smapInner(autInner.initialState)
    val innerFinal = autInner.acceptingStates.map(smapInner)

    builder.setInitialState(smapOuter(autOuter.initialState))
    for (sf <- autOuter.acceptingStates)
      builder.setAccept(smapOuter(sf), true)

    val epsilons = new MHashMap[autOuter.State, MSet[autOuter.State]]
      with MultiMap[autOuter.State, autOuter.State]

    // copy outer
    for ((s1, lbl, s2) <- autOuter.transitions) {
      val newS1 = smapOuter(s1)
      val newS2 = smapOuter(s2)

      for (newLbl <- autOuter.LabelOps.subtractLetter(toReplace, lbl)) {
        builder.addTransition(newS1, newLbl, newS2)
      }

      if (autOuter.LabelOps.labelContains(toReplace, lbl)) {
        epsilons.addBinding(newS1, innerInit)
        for (sf <- innerFinal)
          epsilons.addBinding(sf, newS2)
      }
    }

    // copy inner
    for ((s1, lbl, s2) <- autInner.transitions) {
      val newS1 = smapInner(s1)
      val newS2 = smapInner(s2)
      val convL = lbl.asInstanceOf[autOuter.TLabel]
      builder.addTransition(newS1, convL, newS2)
    }

    buildEpsilons(builder, epsilons)

    builder.getAutomaton
  }

  /**
    * Continue a build by providing epsilon transitions.
    * Note, adding new transitions after calling this will invalidate the
    * results of this function
    *
    * @param builder the builder to add transitions to
    * @param epsilons epsilons(q) = set of q' where there is an e-transition from q to q'
    */
  def buildEpsilons[State, TLabel](
      builder: AtomicStateAutomatonBuilder[State, TLabel],
      epsilons: MultiMap[State, State]
  ): Unit = {
    // transitive closes (modifies in place) the map representing a list
    // of pairs (x, y)
    def tranClose[A](pairs: MultiMap[A, A]): MultiMap[A, A] = {
      val worklist = new MStack[(A, A)]
      val closure = new MHashMap[A, MSet[A]] with MultiMap[A, A]

      for ((x, ys) <- pairs; y <- ys) {
        worklist.push((x, y))
        closure.addBinding(x, y)
      }

      while (!worklist.isEmpty) {
        val (x, y) = worklist.pop
        for (z <- pairs.getOrElse(y, List()); if !closure(x).contains(z)) {
          closure.addBinding(x, z)
          worklist.push((x, z))
        }
      }

      closure
    }

    val closure = tranClose(epsilons)
    for ((ps1, ps2s) <- closure; ps2 <- ps2s; if (ps1 != ps2)) {
      if (builder.isAccept(ps2))
        builder.setAccept(ps1, true)

      for ((ps3, lbl) <- builder.outgoingTransitions(ps2)) {
        builder.addTransition(ps1, lbl, ps3)
      }
    }
  }

// huzi add---------------------------------------------------------------------------------
  def buildEpsilons[State, TLabel](
      builder: AtomicStateAutomatonBuilder[State, TLabel],
      epsilons: MultiMap[State, (State, List[Int])],
      isAddEtaMap: Boolean
  ): Unit = {
    // transitive closes (modifies in place) the map representing a list
    // of pairs (x, y)
    if (!builder.isInstanceOf[BricsAutomatonBuilder])
      throw new Exception("builder is not a BricsAutomatonBuilder")
    def tranClose[A](
        pairs: MultiMap[A, (A, List[Int])]
    ): MultiMap[A, (A, List[Int])] = {
      val worklist = new MStack[(A, (A, List[Int]))]
      val closure = new MHashMap[A, MSet[(A, List[Int])]]
        with MultiMap[A, (A, List[Int])]

      for ((x, ys) <- pairs; y <- ys) {
        worklist.push((x, y))
        closure.addBinding(x, y)
      }

      while (!worklist.isEmpty) {
        val (x, y) = worklist.pop
        for (z <- pairs.getOrElse(y._1, List()); if !closure(x).contains(z)) {
          closure.addBinding(x, z)
          worklist.push((x, z))
        }
      }

      closure
    }
    val etaMap = new MHashMap[
      (BricsAutomaton#State, BricsAutomaton#TLabel, BricsAutomaton#State),
      List[Int]
    ]

    val closure = tranClose(epsilons)
    for ((ps1, ps2s) <- closure; (ps2, v) <- ps2s; if (ps1 != ps2)) {
      if (builder.isAccept(ps2))
        builder.setAccept(ps1, true)

      for ((ps3, lbl) <- builder.outgoingTransitions(ps2)) {
        builder
          .asInstanceOf[BricsAutomatonBuilder]
          .addTransition(
            ps1.asInstanceOf[BricsAutomaton#State],
            lbl.asInstanceOf[BricsAutomaton#TLabel],
            ps3.asInstanceOf[BricsAutomaton#State],
            v
          )
      }
    }
  }
}

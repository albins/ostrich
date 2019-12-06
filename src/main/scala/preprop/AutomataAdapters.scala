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

import ap.parser.ITerm

import scala.collection.mutable.{
  ArrayBuffer,
  ArrayStack,
  MultiMap,
  HashMap => MHashMap,
  HashSet => MHashSet,
  LinkedHashSet => MLinkedHashSet,
  Set => MSet
}
import scala.collection.{Set => GSet}
import dk.brics.automaton.{State => BState}

object AtomicStateAutomatonAdapter {
  def intern(a: Automaton): Automaton = a match {
    case a: AtomicStateAutomatonAdapter[_] => a.internalise
    case a                                 => a
  }
  def intern(a: AtomicStateAutomaton): AtomicStateAutomaton = a match {
    case a: AtomicStateAutomatonAdapter[_] => a.internalise
    case a                                 => a
  }
}

abstract class AtomicStateAutomatonAdapter[A <: AtomicStateAutomaton](
    val underlying: A
) extends AtomicStateAutomaton {

  import AtomicStateAutomatonAdapter.intern

  type State = underlying.State
  type TLabel = underlying.TLabel
  override val LabelOps = underlying.LabelOps

  def |(that: Automaton): Automaton =
    intern(this) | intern(that)
  def &(that: Automaton): Automaton =
    intern(this) & intern(that)

  def unary_! : Automaton =
    !intern(this)

  def isEmpty: Boolean =
    !AutomataUtils.areConsistentAtomicAutomata(List(this))

  def apply(word: Seq[Int]): Boolean =
    internalise.apply(word) // TODO: optimise

  def getAcceptedWord: Option[Seq[Int]] =
    internalise.getAcceptedWord // TODO: optimise

  def toDetailedString: String = underlying.toDetailedString

  protected def computeReachableStates(
      initState: State,
      accStates: Set[State]
  ): GSet[State] = {
    val fwdReachable, bwdReachable = new MLinkedHashSet[State]
    fwdReachable += initState

    val worklist = new ArrayStack[State]
    worklist push initState

    while (!worklist.isEmpty) for ((s, _) <- underlying.outgoingTransitions(
                                     worklist.pop
                                   ))
      if (fwdReachable add s)
        worklist push s

    val backMapping = new MHashMap[State, MHashSet[State]]

    for (s <- fwdReachable)
      for ((t, _) <- underlying.outgoingTransitions(s))
        backMapping.getOrElseUpdate(t, new MHashSet) += s

    for (_s <- accStates; s = _s.asInstanceOf[State])
      if (fwdReachable contains s) {
        bwdReachable += s
        worklist push s
      }

    while (!worklist.isEmpty) for (list <- backMapping get worklist.pop;
                                   s <- list)
      if (bwdReachable add s)
        worklist push s

    if (bwdReachable.isEmpty)
      bwdReachable add initState

    bwdReachable
  }

  def internalise: AtomicStateAutomaton = underlying match {
    // hu zi add -------------------------------------------------------------
    case a: BricsAutomaton => {
      type Transition =
        (BricsAutomaton#State, BricsAutomaton#TLabel, BricsAutomaton#State)
      val builder = a.getBuilder
      val smap = new MHashMap[underlying.State, a.State]
      val etaMap = new MHashMap[Transition, List[Int]]

      for (s <- states)
        smap.put(s, builder.getNewState)

      for (s <- states) {
        val t = smap(s)
        for ((to, label) <- outgoingTransitions(s)) {
          val transition = (
            s.asInstanceOf[BricsAutomaton#State],
            label.asInstanceOf[BricsAutomaton#TLabel],
            to.asInstanceOf[BricsAutomaton#State]
          )
          val vector = a.etaMap(transition)

          builder.addTransition(
            t,
            label.asInstanceOf[BricsAutomaton#TLabel],
            smap(to),
            vector
          )
          // val builderTransition = (t.asInstanceOf[BricsAutomaton#State],
          //   label.asInstanceOf[BricsAutomaton#TLabel],
          //   smap(to).asInstanceOf[BricsAutomaton#State])
          // etaMap += (builderTransition -> vector)
        }
        builder.setAccept(t, isAccept(s))
      }

      builder.setInitialState(smap(initialState))

      val res = builder.getAutomaton
      res.asInstanceOf[BricsAutomaton].addEtaMaps(builder.etaMap)
      res.asInstanceOf[BricsAutomaton].setRegisters(registers)
      res
    }
    // hu zi add -------------------------------------------------------------
  }

  def getTransducerBuilder: TransducerBuilder[State, TLabel] =
    underlying.getTransducerBuilder

  def getBuilder: AtomicStateAutomatonBuilder[State, TLabel] =
    underlying.getBuilder

  def isAccept(s: State): Boolean =
    acceptingStates contains s

  // The fellowing fields can be redefined to modify the automaton

  lazy val initialState = underlying.initialState

  lazy val states = underlying.states

  lazy val acceptingStates = underlying.acceptingStates

  lazy val labelEnumerator = underlying.labelEnumerator

  def outgoingTransitions(from: State): Iterator[(State, TLabel)] =
    underlying.outgoingTransitions(from)

  // huzi add
  override val registers = underlying.registers
}

////////////////////////////////////////////////////////////////////////////////

object InitFinalAutomaton {
  def apply[A <: AtomicStateAutomaton](
      aut: A,
      initialState: A#State,
      acceptingStates: Set[A#State]
  ): AtomicStateAutomaton =
    aut match {
      case _InitFinalAutomaton(a, _, _) =>
        _InitFinalAutomaton(
          a,
          initialState.asInstanceOf[AtomicStateAutomaton#State],
          acceptingStates.asInstanceOf[Set[AtomicStateAutomaton#State]]
        )
      case _ =>
        _InitFinalAutomaton(aut, initialState, acceptingStates)
    }

  def setInitial[A <: AtomicStateAutomaton](aut: A, initialState: A#State) =
    aut match {
      case _InitFinalAutomaton(a, oldInit, oldFinal) =>
        _InitFinalAutomaton(a, initialState, oldFinal)
      case _ =>
        _InitFinalAutomaton(
          aut,
          initialState,
          aut.acceptingStates.asInstanceOf[Set[AtomicStateAutomaton#State]]
        )
    }

  def setFinal[A <: AtomicStateAutomaton](
      aut: A,
      acceptingStates: Set[AtomicStateAutomaton#State]
  ) =
    aut match {
      case _InitFinalAutomaton(a, oldInit, oldFinal) =>
        _InitFinalAutomaton(a, oldInit, acceptingStates)
      case _ =>
        _InitFinalAutomaton(aut, aut.initialState, acceptingStates)
    }
}

/**
  * Representation of automaton with initial and final states changed
  *
  * See InitFinalAutomaton for building
  */
case class _InitFinalAutomaton[A <: AtomicStateAutomaton](
    _underlying: A,
    val _initialState: A#State,
    val _acceptingStates: Set[A#State]
) extends AtomicStateAutomatonAdapter[A](_underlying) {
  import AtomicStateAutomatonAdapter.intern

  override lazy val initialState = _initialState.asInstanceOf[State]

  override lazy val states =
    computeReachableStates(
      _initialState.asInstanceOf[State],
      _acceptingStates.asInstanceOf[Set[State]]
    )

  override lazy val acceptingStates =
    _acceptingStates.asInstanceOf[Set[State]] & states

  override def outgoingTransitions(from: State): Iterator[(State, TLabel)] = {
    val _states = states
    for (p @ (s, _) <- underlying.outgoingTransitions(from);
         if _states contains s)
      yield p
  }
  // huzi add
  override val registers =
    _underlying.asInstanceOf[BricsAutomaton].cloneRegisters

}

/**
  * Case class representation of AutomataUtils.replaceTransitions
  */
case class ReplaceCharAutomaton[A <: AtomicStateAutomaton](
    aut: A,
    a: Char,
    newTrans: Iterable[(A#State, A#State)]
) extends AtomicStateAutomatonAdapter[AtomicStateAutomaton](
      AutomataUtils.replaceTransitions(aut, a, newTrans)
    ) {}

/**
  * Facade for _ProductAutomaton that just returns the automaton if only
  * one is given, else products the given automata
  */
object ProductAutomaton {
  def apply(auts: Seq[AtomicStateAutomaton]): AtomicStateAutomaton = {
    if (auts.size == 1)
      auts(0)
    else
      _ProductAutomaton(auts)
  }
}

/**
  * Case class representation of AutomataUtils.product, see
  * ProductAutomaton
  */
case class _ProductAutomaton(auts: Seq[AtomicStateAutomaton])
    extends AtomicStateAutomatonAdapter[AtomicStateAutomaton](
      AutomataUtils.product(auts)
    ) {}

/**
  * Case class representation of tran.preImage(aut, internal)
  */
case class PreImageAutomaton[A <: AtomicStateAutomaton](
    tran: Transducer,
    targ: A,
    internal: Iterable[(A#State, A#State)]
) extends AtomicStateAutomatonAdapter[AtomicStateAutomaton](
      // extends AtomicStateAutomatonAdapter[A](
      tran.preImage(targ, internal)
    ) {}

/**
  * Case class representation of tran.preImage(aut, internalAut)
  */
case class PostImageAutomaton[A <: AtomicStateAutomaton](
    inAut: A,
    tran: Transducer,
    internalAut: Option[A] = None
) extends AtomicStateAutomatonAdapter[AtomicStateAutomaton](
      // extends AtomicStateAutomatonAdapter[A](
      tran.postImage(inAut, internalAut)
    ) {}

/**
  * Case class representation of AutomataUtils.reverse
  */
case class ReverseAutomaton(aut: AtomicStateAutomaton)
    extends AtomicStateAutomatonAdapter[AtomicStateAutomaton](
      AutomataUtils.reverse(aut)
    ) {}

/**
  * Case class representation of AutomataUtils.reverse
  */
case class ConcatAutomaton(
    aut1: AtomicStateAutomaton,
    aut2: AtomicStateAutomaton
) extends AtomicStateAutomatonAdapter[AtomicStateAutomaton](
      AutomataUtils.concat(aut1, aut2)
    ) {}

/**
  * Case class representation of one automaton inserted into another to
  * replace a-transitions.  See AutomatonUtils.nestAutomata.
  */
case class NestedAutomaton(
    inner: AtomicStateAutomaton,
    a: Char,
    outer: AtomicStateAutomaton
) extends AtomicStateAutomatonAdapter[AtomicStateAutomaton](
      AutomataUtils.nestAutomata(inner, a, outer)
    ) {}

// huzi add ----------------------------------------------------------------------
/**
  * Case class representation of AutomataUtils.reverse
  */
case class ReverseBAutomaton(aut: BricsAutomaton)
    extends AtomicStateAutomatonAdapter[BricsAutomaton](
      AutomataUtils.reverse(aut)
    ) {}
// huzi add ----------------------------------------------------------------------

package strsolver
import ap.basetypes.IdealInt
import ap.parser._
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.terfor.TerForConvenience._
import ap.terfor.preds.Atom
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.{Formula, TermOrder}
import ap.theories._
import strsolver.preprop.BricsAutomaton
import strsolver.preprop.EdgeWrapper._
import strsolver.preprop.{RichGraph, Graphable}
import ap.parser.IExpression.Predicate

trait NoFunctions {
  val functionPredicateMapping
      : Seq[(ap.parser.IFunction, ap.parser.IExpression.Predicate)] = List()
  val functionalPredicates: Set[ap.parser.IExpression.Predicate] = Set()
  val functions: Seq[ap.parser.IFunction] = List()
  val predicateMatchConfig: ap.Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions: Set[ap.parser.IFunction] = Set()
}

trait NoAxioms {
  val axioms: Formula = Conjunction.TRUE
  val totalityAxioms: ap.terfor.Formula = Conjunction.TRUE
}

trait Tracing {
  protected def trace[T](message: String)(something: T): T = {
    // println(s"trace::${message}(${something})")
    something
  }
}

trait Complete extends Theory {
  override def isSoundForSat(
      theories: Seq[Theory],
      config: Theory.SatSoundnessConfig.Value
  ): Boolean =
    Set(
      Theory.SatSoundnessConfig.Elementary,
      Theory.SatSoundnessConfig.Existential
    ) contains config
}

trait NoAxiomGeneration {
  def generateAxioms(goal: Goal) = None
}

// Provide a function to handle a predicate, automatically become a theory
// procedure.
trait PredicateHandlingProcedure extends TheoryProcedure {
  val procedurePredicate: IExpression.Predicate
  def handlePredicateInstance(goal: Goal)(
      predicateAtom: Atom
  ): Seq[Plugin.Action]

  override def handleGoal(goal: Goal): Seq[Plugin.Action] =
    goal.facts.predConj
      .positiveLitsWithPred(procedurePredicate)
      .flatMap(handlePredicateInstance(goal))
}

class ParikhTheory(private[this] val aut: BricsAutomaton)
    extends Theory
    with NoFunctions
    with NoAxioms
    with Tracing
    with Complete {

  private val cycles = aut.simpleCycles
  trace("cycles")(cycles.map(_.map(aut.state2Index)))

  private val cutAndCycle = cycles.flatMap { cycle =>
    trace("cycle head")(aut.state2Index(cycle.last))
    val cycleMerged = aut.mergeNodes(cycle)
    val initialState = cycleMerged equivalentNode aut.initialState
    val cycleState = cycleMerged equivalentNode cycle.last
    if (initialState == cycleState) List()
    else {
      val connectingEdges =
        cycleMerged
          .minCut(
            initialState,
            cycleState
          )
          .flatMap { case (_, realEdges, _) => realEdges }

      trace("connectingEdges")(connectingEdges.map(aut.fmtTransition))

      if (connectingEdges.isEmpty) List() else List((connectingEdges, cycle))
    }

  }.toIndexedSeq

  trace("cutAndCycle")(cutAndCycle.map {
    case (cut, cycle) =>
      (cut.map(aut.fmtTransition), cycle.map(aut.state2Index))
  })

  // This describes the status of a transition in the current model
  protected sealed trait TransitionSelected {
    def definitelyAbsent = false
    def isUnknown = false
  }

  object TransitionSelected {
    case object Present extends TransitionSelected
    case object Absent extends TransitionSelected {
      override def definitelyAbsent = true
    }
    case object Unknown extends TransitionSelected {
      override def isUnknown = true
    }
  }

  private object TransitionSplitter extends PredicateHandlingProcedure {
    override val procedurePredicate = predicate
    override def handlePredicateInstance(
        goal: Goal
    )(predicateAtom: Atom): Seq[Plugin.Action] = {
      implicit val _ = goal.order

      val transitionTerms = trace("transitionTerms") {
        predicateAtom.take(aut.transitions.size)
      }

      val unknownTransitions = trace("unknownTransitions") {
        transitionTerms filter (
            t => transitionStatusFromTerm(goal, t).isUnknown
        )
      }

      trace("unknownActions") {
        def transitionToSplit(transitionTerm: LinearCombination) =
          Plugin.SplitGoal(
            Seq(transitionTerm === 0, transitionTerm > 0)
              .map(eq => Seq(Plugin.AddFormula(conj(eq))))
          )

        val splittingActions = trace("splittingActions") {
          unknownTransitions
            .map(transitionToSplit(_))
            .toList
        }

        splittingActions

      }
    }
  }

  private object ConnectednessPropagator
      extends Plugin
      with PredicateHandlingProcedure
      with NoAxiomGeneration {
    // Handle a specific predicate instance for a proof goal, returning the
    // resulting plugin actions.
    override val procedurePredicate = predicate
    override def handlePredicateInstance(
        goal: Goal
    )(predicateAtom: Atom): Seq[Plugin.Action] = {
      implicit val _ = goal.order

      val transitionTerms = predicateAtom.take(aut.transitions.size)

      val transitionToTerm =
        aut.transitions.to.zip(transitionTerms).toMap

      trace("transitionToTerm") {
        transitionToTerm.map {
          case (transition, term) =>
            s"${aut.fmtTransition(transition)} == ${term}"
        }

      }

      val splittingActions = trace("splittingActions") {
        goalState(goal) match {
          case Plugin.GoalState.Final => TransitionSplitter.handleGoal(goal)
          case _                      => List(Plugin.ScheduleTask(TransitionSplitter, 0))
        }
      }

      // TODO check if we are subsumed (= if there are no unknown transitions);
      // then generate a Plugin.RemoveFacts with the generated atoms. Should
      // amount to checking if unknown transitions is None.

      // TODO: we don't care about splitting edges that cannot possibly cause a
      // disconnect; i.e. *we only care* about critical edges on the path to
      // some cycle that can still appear (i.e. wose edges are not
      // known-deselected).

      // constrain any terms associated with a transition from a
      // *known* unreachable state to be = 0 ("not used").
      val unreachableActions = trace("unreachableActions") {
        val deadTransitions = trace("deadTransitions") {
          aut.transitions
            .filter(
              t => termMeansDefinitelyAbsent(goal, transitionToTerm(t))
            )
            .to[Set]
        }

        val unreachableConstraints =
          conj(
            aut
              .dropEdges(deadTransitions)
              .unreachableFrom(aut.initialState)
              .flatMap(
                aut.transitionsFrom(_).map(transitionToTerm(_) === 0)
              )
          )

        if (unreachableConstraints.isTrue) Seq()
        else Seq(Plugin.AddFormula(!unreachableConstraints))
      }

      unreachableActions ++ splittingActions
    }
  }

  // FIXME: total deterministisk ordning på edges!
  // FIXME: name the predicate!
  private val predicate =
    new Predicate(s"pa-${aut.hashCode}", aut.edges.size + aut.registers.size)

  val predicates: Seq[ap.parser.IExpression.Predicate] = List(predicate)

  override def preprocess(f: Conjunction, order: TermOrder): Conjunction = {
    implicit val newOrder = order

    def asManyIncomingAsOutgoing(
        transitionAndVar: Seq[(aut.FromLabelTo, LinearCombination)]
    ): Formula = {
      def asStateFlowSum(
          stateTerms: Seq[(aut.State, (IdealInt, LinearCombination))]
      ) = {
        val (state, _) = stateTerms.head
        val isInitial =
          (if (state == aut.initialState) LinearCombination.ONE
           else LinearCombination.ZERO)
        (state, sum(stateTerms.unzip._2 ++ List((IdealInt.ONE, isInitial))))
      }

      trace("Flow equations") {
        conj(
          transitionAndVar
            .filter(!_._1.isSelfEdge)
            .flatMap {
              case ((from, _, to), transitionVar) =>
                List(
                  (to, (IdealInt.ONE, transitionVar)),
                  (from, (IdealInt.MINUS_ONE, transitionVar))
                )
            }
            .to
            .groupBy(_._1)
            .values
            .map(asStateFlowSum)
            .map {
              case (state, flowSum) =>
                if (state.isAccept) flowSum >= 0 else flowSum === 0
            }
        )
      }
    }

    def registerValuesReachable(
        registerVars: Seq[LinearCombination],
        transitionAndVar: Seq[(aut.FromLabelTo, LinearCombination)]
    ): Formula = {
      trace("Register equations") {
        conj(registerVars.zipWithIndex.map {
          case (rVar, rIdx) =>
            rVar === sum(transitionAndVar.map {
              case (t, tVar) =>
                (IdealInt.int2idealInt(aut.etaMap(t)(rIdx)), tVar)
            })
        })

      }
    }

    def allNonnegative(vars: Seq[LinearCombination]) = conj(vars.map(_ >= 0))

    Theory.rewritePreds(f, order) { (atom, _) =>
      if (atom.pred == this.predicate) {
        val (transitionVars, registerVars) = atom.splitAt(aut.transitions.size)
        val transitionAndVar = aut.transitions.zip(transitionVars.iterator).to

        val constraints = List(
          asManyIncomingAsOutgoing(transitionAndVar),
          allNonnegative(transitionVars),
          allNonnegative(registerVars),
          registerValuesReachable(registerVars, transitionAndVar)
        )

        val maybeAtom = if (cutAndCycle.isEmpty) List() else List(atom)

        trace(s"Rewriting predicate ${atom} => \n") {
          Conjunction.conj(maybeAtom ++ constraints, order)
        }
      } else atom
    }
  }

  private def termMeansDefinitelyAbsent(
      goal: Goal,
      term: LinearCombination
  ): Boolean = trace(s"termMeansDefinitelyAbsent(${term})") {
    term match {
      case LinearCombination.Constant(x) => x <= 0
      case _                             => goal.reduceWithFacts.upperBound(term).exists(_ <= 0)
    }

  }

  private[this] def transitionStatusFromTerm(
      goal: Goal,
      term: LinearCombination
  ): TransitionSelected = trace(s"selection status for ${term} is ") {
    lazy val lowerBound = goal.reduceWithFacts.lowerBound(term)
    lazy val upperBound = goal.reduceWithFacts.upperBound(term)

    if (lowerBound.exists(_ > 0)) TransitionSelected.Present
    else if (upperBound.exists(_ <= 0)) TransitionSelected.Absent
    else TransitionSelected.Unknown
  }

  def plugin: Option[Plugin] = Some(ConnectednessPropagator)

  /**
    * Generate a quantified formula that is satisfiable iff the provided
    * register values are possible by any legal path through the automaton.
    *
    **/
  def allowsRegisterValues(registerValues: Seq[ITerm]): IFormula = {
    import IExpression._
    val transitionTermSorts = List.fill(aut.edges.size)(Sort.Integer) //
    val transitionTerms = aut.edges.indices.map(v)
    ex(
      transitionTermSorts,
      this.predicate(transitionTerms ++ registerValues: _*)
    )
  }

  TheoryRegistry register this

}

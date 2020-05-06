package strsolver
import ap.basetypes.IdealInt
import ap.parser._
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.TerForConvenience._
import ap.terfor.preds.Atom
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.{Formula, TermOrder}
import ap.theories._
import strsolver.preprop.BricsAutomaton
import strsolver.preprop.EdgeWrapper._

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

class ParikhTheory(private[this] val aut: BricsAutomaton)
    extends Theory
    with NoFunctions
    with NoAxioms
    with Tracing
    with Complete {
  import IExpression.Predicate

  // This describes the status of a transition in the current model
  protected sealed trait TransitionSelected {
    def definitelyAbsent = false
  }

  object TransitionSelected {
    case object Present extends TransitionSelected
    case object Absent extends TransitionSelected {
      override def definitelyAbsent = true
    }
    case object Unknown extends TransitionSelected
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

        trace(s"Rewriting predicate ${atom} => \n") {
          Conjunction.conj(
            List(
              atom,
              asManyIncomingAsOutgoing(transitionAndVar),
              allNonnegative(transitionVars),
              allNonnegative(registerVars),
              registerValuesReachable(registerVars, transitionAndVar)
            ),
            order
          )
        }
      } else atom
    }
  }

  private[this] def transitionStatusFromTerm(
      goal: Goal,
      term: LinearCombination
  ): TransitionSelected = trace(s"selection status for ${term} is ") {
    term match {
      // The first two cases are an early short-circuit for constants that gets
      // us out of evaluating the whole expression. TODO verify experimentally
      // that this is a good optimisation. Otherwise the function can be simplified!
      case LinearCombination.Constant(x) if x > 0 =>
        TransitionSelected.Present
      case LinearCombination.Constant(x) => TransitionSelected.Absent
      case _ => {
        // FIXME: make this logic short-circuiting!
        val lowerBound = trace("lb")(goal.reduceWithFacts.lowerBound(term))
        val upperBound = trace("ub")(goal.reduceWithFacts.upperBound(term))

        (lowerBound, upperBound) match {
          case (Some(lb), _) if lb > 0  => TransitionSelected.Present
          case (_, Some(ub)) if ub <= 0 => TransitionSelected.Absent
          case _                        => TransitionSelected.Unknown
        }

      }
    }
  }

  // Handle a specific predicate instance for a proof goal, returning the
  // resulting plugin actions.
  private def handlePredicateInstance(
      goal: Goal
  )(predicateAtom: Atom): Seq[Plugin.Action] = {
    implicit val _ = goal.order

    val transitionTerms = trace("transitionTerms") {
      predicateAtom.take(aut.transitions.size)
    }

    val transitionToTerm =
      aut.transitions.to.zip(transitionTerms).toMap

    val transitionByStatus = transitionToTerm
      .groupBy(x => transitionStatusFromTerm(goal, x._2))
      .mapValues(_.keys)

    val unknownActions = trace("unknownActions") {

      val unknownTransitions = trace("unknownTransitions") {
        transitionByStatus get TransitionSelected.Unknown
      }

      def transitionToSplit(transitionTerm: LinearCombination) =
        Plugin.SplitGoal(
          Seq(transitionTerm === 0, transitionTerm > 0)
            .map(eq => Seq(Plugin.AddFormula(conj(eq))))
        )

      val splittingActions = trace("splittingActions") {
        unknownTransitions
          .map(_.map(tr => transitionToSplit(transitionToTerm(tr))))
          .toList
          .flatten
      }

      // TODO check if we are subsumed (= if there are no unknown transitions);
      // then generate a Plugin.RemoveFacts with the generated atoms. Should
      // amount to checking if unknown transitions is None.

      // TODO eventuellt vill vi använda ScheduleTask för att schemalägga en
      // funktion för att köra senare (analogt med Plugin).

      // TODO: we don't care about splitting edges that cannot possibly cause a
      // disconnect; i.e. *we only care* about critical edges on the path to
      // some cycle that can still appear (i.e. wose edges are not
      // known-deselected).

      // if (!splittingActions.isEmpty) Seq(splittingActions.last) else Seq()
      splittingActions

    }

    // constrain any terms associated with a transition from a
    // *known* unreachable state to be = 0 ("not used").
    val unreachableActions = trace("unreachableActions") {
      val deadTransitions = trace("deadTransitions") {
        transitionByStatus.getOrElse(TransitionSelected.Absent, Set()).to[Set]
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

    unreachableActions ++ unknownActions
  }

  def plugin: Option[Plugin] =
    Some(new Plugin with NoAxiomGeneration {
      override def handleGoal(goal: Goal): Seq[Plugin.Action] =
        goal.facts.predConj
          .positiveLitsWithPred(predicate)
          .flatMap(handlePredicateInstance(goal))

    })

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

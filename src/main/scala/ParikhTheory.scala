package strsolver
import ap.basetypes.IdealInt
import ap.parser._
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.TerForConvenience._
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
    println(s"trace::${message}(${something})")
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

class ParikhTheory(private[this] val aut: BricsAutomaton)
    extends Theory
    with NoFunctions
    with NoAxioms
    with Tracing
    with Complete {
  import IExpression.Predicate

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
      } else atom
    }
  }

  def plugin: Option[Plugin] =
    Some(new Plugin {
      def generateAxioms(goal: Goal) = None
      override def handleGoal(goal: Goal): Seq[Plugin.Action] = {
        goal.facts.predConj.positiveLitsWithPred(predicate).flatMap {
          predicateAtom =>
            {
              implicit val _ = goal.order

              val transitionTerms = trace("transitionTerms") {
                predicateAtom.take(aut.transitions.size)
              }

              val transitionToTerm =
                aut.transitions.to.zip(transitionTerms).toMap

              val deadTransitions = transitionToTerm
                .filter {
                  case (_, LinearCombination.Constant(x)) if x <= 0 => true
                  case _                                            => false
                }
                .keys
                .to[Set]

              val unreachableTransitions = aut
                .dropEdges(deadTransitions)
                .unreachableFrom(aut.initialState)
                .flatMap(aut.transitionsFrom(_))

              val unreachableConstraints = trace("unreachableConstraints") {
                conj(unreachableTransitions.map(transitionToTerm(_) === 0))
              }

              // TODO check if we are subsumed; then generate a
              // Plugin.RemoveFacts with the generated atoms

              // TODO splitting; split on different paths through the automaton

              Seq(Plugin.AddFormula(unreachableConstraints))
            }
        }

      }

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

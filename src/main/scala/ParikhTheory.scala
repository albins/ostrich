package strsolver
import ap.theories._
import ap.parser._
import ap.basetypes.IdealInt
import preprop.BricsAutomaton
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{TermOrder, Term, Formula}
import ap.terfor.TerForConvenience._
import ap.terfor.linearcombination.LinearCombination
import strsolver.preprop.EdgeWrapper._

class ParikhTheory(private val aut: BricsAutomaton) extends Theory {
  import IExpression.Predicate

  private def trace[T](message: String)(something: T): T = {
    println(s"trace::${message}(${something})")
    something
  }

  // FIXME: total deterministisk ordning på edges!
  // FIXME: name the predicate!
  private val predicate =
    new Predicate("pa", aut.edges.size + aut.registers.size)

  override def isSoundForSat(
      theories: Seq[Theory],
      config: Theory.SatSoundnessConfig.Value
  ): Boolean =
    Set(
      Theory.SatSoundnessConfig.Elementary,
      Theory.SatSoundnessConfig.Existential
    ) contains config

  // TODO
  // när vi ser ett predikat, ersätt med flow /\ sig själv igen
  // register -> flow equations
  // domänvillkor
  override def preprocess(f: Conjunction, order: TermOrder): Conjunction = {
    // val acceptingStatesArePositive = acceptingStateVar.values.toSeq >= 0
    // val oneAcceptingStateUsed = acceptingStateVar.values.reduce(_ + _) === 1
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
            .map {
              case ((from, _, to), transitionVar) =>
                List(
                  (to, (IdealInt.ONE, transitionVar)),
                  (from, (IdealInt.MINUS_ONE, transitionVar))
                )
            }
            .flatten
            .to
            .groupBy(_._1)
            .values
            .map(asStateFlowSum _)
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

  // BEGIN USELESS BOILERPLATE
  val axioms: Formula = Conjunction.TRUE
  val functionPredicateMapping
      : Seq[(ap.parser.IFunction, ap.parser.IExpression.Predicate)] = List()
  val functionalPredicates: Set[ap.parser.IExpression.Predicate] = Set()
  val functions: Seq[ap.parser.IFunction] = List()
  val predicateMatchConfig: ap.Signature.PredicateMatchConfig = Map()
  val predicates: Seq[ap.parser.IExpression.Predicate] = List(predicate)
  val totalityAxioms: ap.terfor.Formula = Conjunction.TRUE
  val triggerRelevantFunctions: Set[ap.parser.IFunction] = Set()
  // END USELESS BOILERPLATE

  // TODO propagator för connectedness
  def plugin: Option[ap.proof.theoryPlugins.Plugin] = None

  /**
    * Generate a quantified formula that is satisfiable iff the provided
    * register values are possible by any legal path through the automaton.
    *
    **/
  def allowsRegisterValues(registerValues: Seq[ITerm]): IFormula = {
    import IExpression._
    val transitionTermSorts = List.fill(aut.edges.size)(Sort.Integer) //
    val transitionTerms = (0 until aut.edges.size).map(v)
    ex(
      transitionTermSorts,
      this.predicate(transitionTerms ++ registerValues: _*)
    )
  }

  TheoryRegistry register this

}

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

  def trace[T](message: String)(something: T): T = {
    println(s"trace::${message}(${something})")
    something
  }

  // FIXME: total deterministisk ordning på edges!
  // FIXME: name the predicate!
  private val predicate =
    new Predicate("pa", aut.edges.size + aut.registers.size)

  // TODO
  // när vi ser ett predikat, ersätt med flow /\ sig själv igen
  // register -> flow equations
  // domänvillkor
  override def preprocess(f: Conjunction, order: TermOrder): Conjunction = {
    // val acceptingStatesArePositive = acceptingStateVar.values.toSeq >= 0
    // val oneAcceptingStateUsed = acceptingStateVar.values.reduce(_ + _) === 1
    implicit val newOrder = order

    def asManyIncomingAsOutgoing(
        transitionVars: Seq[LinearCombination]
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
          aut.transitions
            .zip(transitionVars.iterator)
            .filter(!_._1.isSelfEdge)
            .map {
              case ((from, _, to), transitionVar) =>
                List(
                  (to, (IdealInt.MINUS_ONE, transitionVar)),
                  (from, (IdealInt.ONE, transitionVar))
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
      // val (acceptingTransitionSums, nonAcceptingTransitionSums) = {
      //   // FIXME This tuple unpacking is...not elegant
      //   val (accept, nonAccept) = transitionSumsByState.partition(_._1.isAccept)
      //   (accept.unzip._2, nonAccept.unzip._2)
      // }

      // // This expresses the constraint that at any transitions in and out from a
      // // non-accepting state are balanced (as many incoming as outgoing
      // // transitions).
      // val nonAcceptingTransitionsBalanced = conj(
      //   nonAcceptingTransitionSums.map(_ === 0)
      // )

      // // This expresses that the transitions in and out of the accepting states
      // // allow ending up on precisely one accepting state.
      // // val acceptingTransitionsBalanced = sum(
      // //   Stream.continually(IdealInt.ONE) zip acceptingTransitionSums
      // // ) === 1
      // val acceptingTransitionsBalanced = conj(
      //   acceptingTransitionSums.map(_ >= 0)
      // )

      // // This propagates a lower bound on the sums that ensures we do not have
      // // "negative" paths.
      // val acceptingTransitionsNotNegative = conj(
      //   acceptingTransitionSums.map(_ >= 0)
      // )

      // trace("Flow equations") {
      //   conj(
      //     nonAcceptingTransitionsBalanced,
      //     acceptingTransitionsBalanced,
      //     acceptingTransitionsNotNegative
      //   )
      // }
    }

    Theory.rewritePreds(f, order) { (atom, negated) =>
      if (atom.pred == this.predicate) {
        Conjunction.conj(
          List(atom, asManyIncomingAsOutgoing(atom.to[Seq])),
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

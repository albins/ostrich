package strsolver
import ap.theories._
import ap.parser._
import preprop.BricsAutomaton
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{TermOrder}

class ParikhTheory(private val aut: BricsAutomaton) extends Theory {
  import IExpression._

  // FIXME: total deterministisk ordning på edges!
  // FIXME: name the predicate!
  private val predicate =
    new Predicate("pa", aut.edges.size + aut.registers.size)

  // TODO
  // när vi ser ett predikat, ersätt med flow /\ sig själv igen
  // register -> flow equations
  // domänvillkor
  override def preprocess(f: Conjunction, order: TermOrder): Conjunction = {
    Theory.rewritePreds(f, order) { (atom, negated) =>
      if (atom.pred == predicate) {
        atom
      } else atom
    }
  }

  // BEGIN USELESS BOILERPLATE
  val axioms: ap.terfor.Formula = Conjunction.TRUE
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
  // TODO ta också BORT predikat när vi är klara med dem
  def plugin: Option[ap.proof.theoryPlugins.Plugin] = None

  /**
    * Generate a quantified formula that is satisfiable iff the provided
    * register values are possible by any legal path through the automaton.
    *
    **/
  def allowsRegisterValues(registerValues: Seq[ITerm]): IFormula = {
    val transitionTermSorts = List.fill(aut.edges.size)(Sort.Integer)
    val transitionTerms = (0 until aut.edges.size).map(v)
    ex(
      transitionTermSorts,
      this.predicate(transitionTerms ++ registerValues: _*)
    )
  }

  TheoryRegistry register this

}

package strsolver

import ap.parser._
import ap.terfor.{Formula, TermOrder}
import ap.terfor.preds.Predicate

//store the input int constraints
object IntConstraintStore {
  private var formula: Formula = _
  private var order: TermOrder = _
  def apply() = formula
  def setFormula(f: Formula): Unit = {
    formula = f
  }
  def setOrder(o: TermOrder): Unit = {
    order = o
  }
  def getOrder : TermOrder = order
}

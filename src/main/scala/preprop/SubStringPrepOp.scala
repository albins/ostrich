package strsolver.preprop
import ap.basetypes.IdealInt
import ap.parser.Internal2InputAbsy
import ap.terfor.Term
import ap.terfor.linearcombination.LinearCombination

object SubStringPreOp{
  def apply(i : Term, j : Term, resLen : Term) : PreOp = {
    new SubStringPreOp(i,j,resLen)
  }
}

class SubStringPreOp(i : Term, j : Term, resLen : Term) extends PreOp{
  // TODO : add logic
	def apply(argumentConstraints : Seq[Seq[Automaton]],
            resultConstraint : Automaton)
          : (Iterator[(Seq[Automaton], LinearConstraints)], Seq[Seq[Automaton]]) = {
    val input_i = Internal2InputAbsy(i)
    val input_j = Internal2InputAbsy(j)
    val input_resLen = Internal2InputAbsy(resLen)
    var resList = List()
    val a = new LinearConstraints
    val resAut = AtomicStateAutomatonAdapter.intern(resultConstraint).asInstanceOf[BricsAutomaton]
    // "" = substring(x, i, j)
    if(resAut.underlying.isEmptyString()){
//       i<0 | j <= 0 | i >= len(x)
      a.addFormula((input_i < 0) | (input_j<=0) |(input_i >= input_resLen))
      return (Iterator((Seq(BricsAutomaton.makeAnyString()), a)), List())
    }

    val builder = resAut.getBuilder
    val infiniteCycleS = builder.getNewState
    builder.setAccept(infiniteCycleS, true)
    val resAutRLen = resAut.registers.size    // resAut registers size
    val tmpList = List.fill(resAutRLen)(0)
    val sigma = builder.LabelOps.sigmaLabel

    val resAutSLen = resAut.states.size       // resAut states size
    val states1 = List.fill(resAutSLen)(builder.getNewState)
    // from resAut states map to new states
    val sMap = (resAut.states zip states1).toMap
    val initState = builder.getNewState
    builder.setInitialState(initState)
    val resInit = resAut.initialState
    if(resAut.isAccept(resInit))
    builder.setAccept(initState, true)

    var needIFCS : Boolean = false
    // add transition from resAut initState
    for((ts, (charMin, charMax)) <- resAut.outgoingTransitions(resInit)){
      val vector = resAut.etaMap((resInit, (charMin,charMax), ts))
      builder.addTransition(initState, (charMin,charMax), sMap(ts), List(0,1)++vector)
    }

    builder.addTransition(initState, sigma, initState, List(1,1)++tmpList)

    var resInitArrivable = false
    for((_, _, to) <- resAut.transitions){
      if(to == resInit)
      resInitArrivable = true
    }
    for(fs <- resAut.states){
      val fsIsAccept = resAut.isAccept(fs)
      builder.setAccept(sMap(fs), fsIsAccept)
      if(resInitArrivable || fs != resInit) {
        // if resInit not arrivable,
        // resInit's transition has already been added above
        for ((ts, label) <- resAut.outgoingTransitions(fs)) {
          val vector = resAut.etaMap((fs, label, ts))
          builder.addTransition(sMap(fs), label, sMap(ts), List(0, 1) ++ vector)
        }
        if (fsIsAccept)
        if (builder.etaMap.contains((sMap(fs), sigma, sMap(fs)))) {
          needIFCS = true
          builder.addTransition(sMap(fs), sigma, infiniteCycleS, List(0, 0) ++ tmpList)
        } else
        builder.addTransition(sMap(fs), sigma, sMap(fs), List(0, 0) ++ tmpList)
      }
    }
    if(needIFCS)
    builder.addTransition(infiniteCycleS,sigma,infiniteCycleS, List(0,0)++tmpList)
    val res = builder.getAutomaton
    res.addEtaMaps(builder.etaMap)
    res.addNewRegister(2)   // i,j
    res.addRegisters(resAut.registers)  // New registers is (i, j)++resAut.registers
    a.addFormula( ( (
      (res.registers(1) === (input_i+input_j)) & // for cvc4 , j is offset, position is i+j
    (res.registers(1) <= input_resLen)
    ) |
    (
      (res.registers(1) === input_resLen) &
    ((input_i+input_j) > input_resLen)   // for cvc4, if i+j > s.len, the substr(s,i, s.len)
    )
    ) & (res.registers(0) === input_i)
    )

    if(resAut.underlying.getShortestExample(true) == ""){
      // when resAut contains "", we need two choice,
      val b = new LinearConstraints
      b.addFormula((input_i < 0) | (input_j<=0) |(input_i >= input_resLen))
      val resList = List((Seq(BricsAutomaton.makeAnyString()), b)) :+ ((Seq(res), a))
      return  (resList.toIterator, List())
    }
    (Iterator((Seq(res), a)), List())
  }

  def eval(arguments : Seq[Seq[Int]]) : Option[Seq[Int]] = {

    val strLen = arguments(0).size
      val i_option = IdealInt.unapply(i.asInstanceOf[LinearCombination].constant)
      val j_option = IdealInt.unapply(j.asInstanceOf[LinearCombination].constant)
      if (i_option == None || j_option == None)
        return None
      val i_value = i_option.get
      val j_value = j_option.get
      if(i_value < 0 || j_value > strLen-1)
        return None

      return Some(arguments(0).slice(i_value, j_value))

    }
 	override def toString = "substring{"+i.toString+","+j.toString+"}"

}
package strsolver

import org.scalatest.FunSuite
import org.scalatest.Assertions._
import strsolver.preprop.{BricsAutomaton, BricsAutomatonBuilder}
import ap.terfor.{Formula}

class TestParikhTheory extends FunSuite {

  private def verifyRegisterValues(aut: BricsAutomaton, allowedRegisterValues: Seq[Seq[Int]]) {
    import ap.PresburgerTools
    import ap.SimpleAPI
    import ap.parser.{
      IConstant,
      ITerm,
      InputAbsy2Internal,
      Internal2InputAbsy,
      IExpression,
      IFormula
    }
    import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}

    SimpleAPI.withProver { p =>
      import p._

      val registerVars = aut.registers.zip(allowedRegisterValues).map {
        case (_, allowedValues) => {
          val c = createConstant
          allowedValues.foreach(v => addAssertion (c =/= v))
          c
        }
      }

      addAssertion((new ParikhTheory(aut)) allowsRegisterValues (registerVars))

      if (??? != SimpleAPI.ProverStatus.Unsat) {
        assert(false, s"${???}. Countermodel: ${partialModel}")
      }

    }
  }

  private val allChars: (Char, Char) = (0, 65535)


  //              R1  += 3
  //       +--------------------------------+
  //       |                                v
  //     +---+ R1  += 2   #===# R1  +=5   #===#
  // --> | 0 | ---------> H 1 H --------> H 2 H
  //     +---+            #===#           #===#
  test("3-state, 1-register loop-free automaton has correct register values") {
    val builder = new BricsAutomatonBuilder
    val states = (0 to 2)
      .map(i => {
             val s = builder.getNewState;
             if (i != 0) builder.setAccept(s, true);
             s
           })
      .to[Array]

    val stateIndex = states.zipWithIndex.toMap

    builder.setInitialState(states(0))

    builder.addTransition(states(0), allChars, states(1), List(2))
    builder.addTransition(states(0), allChars, states(2), List(3))
    builder.addTransition(states(1), allChars, states(2), List(5))

    val automaton = {
      val a = builder.getAutomaton
      a.addEtaMaps(builder.etaMap)
      a.addNewRegister(builder.etaMap(a.transitions.next).size)
      a
    }

    println(automaton.toDot)
    println(automaton.transitions.map{case(from, _, to) =>
              (stateIndex(from), stateIndex(to))}.to[Seq])
    verifyRegisterValues(automaton, List(List(2, 3, 7)))

  }

}

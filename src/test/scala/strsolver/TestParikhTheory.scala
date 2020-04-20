package strsolver

import org.scalatest.FunSuite
import org.scalatest.Assertions._
import strsolver.preprop.{BricsAutomaton, BricsAutomatonBuilder}
import ap.terfor.{Formula}
import ap.parser.ITerm

class TestParikhTheory extends FunSuite {

  private def expectUnsatRegisterConstraints(aut: BricsAutomaton, comment: String = "")(constraintGenerator: (Seq[ITerm], ap.SimpleAPI) => Unit) {
    import ap.PresburgerTools
    import ap.SimpleAPI
    import ap.parser.{
      IConstant,
      InputAbsy2Internal,
      Internal2InputAbsy,
      IExpression,
      IFormula
    }
    import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}

    SimpleAPI.withProver { p =>
      import p._

      val registerVars = aut.registers.map(_ => createConstant)

      constraintGenerator(registerVars, p)

      addAssertion((new ParikhTheory(aut)) allowsRegisterValues (registerVars))

      if (??? != SimpleAPI.ProverStatus.Unsat) {
        assert(false, s"${comment}: ${???}. Countermodel: ${partialModel}")
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

    // println(automaton.toDot)
    println(automaton.transitions.map{case(from, _, to) =>
              (stateIndex(from), stateIndex(to))}.to[Seq])

    expectUnsatRegisterConstraints(automaton) {
      case (registers, p) =>
        val r = registers(0)
        List(2, 3, 7).foreach(v => p.addAssertion(r =/= v))
    }

  }


  //              #3
  //         +---------+
  //         v         |
  //       +---+  #0 +---+  #2 +---+
  //   --> | 0 | --> | 1 | --> | 3 | -->
  //       +---+     +---+     +---+
  //         |                 | ^
  //         | #1       #5     | |
  //         v     +-----------+ |
  //       +---+<--+    #4       |
  //       | 2 | ----------------+
  //       +---+
  //       |   ^
  //       +---+
  //         #6
  test("4-state, per-transition register automaton with loop has correct values") {
    val builder = new BricsAutomatonBuilder
    val states = (0 to 3).map(_ => builder.getNewState).to[Array]
    val stateIndex = states.zipWithIndex.toMap

    builder.setAccept(states(3), true)
    builder.setInitialState(states(0))

    builder.addTransition(states(0), allChars, states(1), List(1, 0, 0, 0, 0, 0, 0))
    builder.addTransition(states(0), allChars, states(2), List(0, 1, 0, 0, 0, 0, 0))

    builder.addTransition(states(1), allChars, states(3), List(0, 0, 1, 0, 0, 0, 0))
    builder.addTransition(states(1), allChars, states(0), List(0, 0, 0, 1, 0, 0, 0))

    builder.addTransition(states(2), allChars, states(3), List(0, 0, 0, 0, 1, 0, 0))
    builder.addTransition(states(2), allChars, states(2), List(0, 0, 0, 0, 0, 0, 1))

    builder.addTransition(states(3), allChars, states(2), List(0, 0, 0, 0, 0, 1, 0))

    val aut = {
      val a = builder.getAutomaton
      a.addEtaMaps(builder.etaMap)
      a.addNewRegister(builder.etaMap(a.transitions.next).size)
      a
    }

    // println(automaton.toDot)
    println(aut.transitions.map{case(from, _, to) =>
              (stateIndex(from), stateIndex(to))}.to[Seq])

    expectUnsatRegisterConstraints(aut, "#3 >= 1 & #0 < 1") {
      case (r, p) => p.addAssertion((r(3) >= 1) &&& (r(0) ===  0))
    }

    expectUnsatRegisterConstraints(aut, "#6 disconnected") {
      case (r, p) => p.addAssertion((r(6) >= 1) &&& (r(5) === 0) &&& (r(1) === 0))
    }


  }

}

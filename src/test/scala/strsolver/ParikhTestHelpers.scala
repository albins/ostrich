package strsolver
import ap.terfor.Formula
import org.scalatest.Assertions._
import strsolver.preprop.{BricsAutomaton, BricsAutomatonBuilder}

object ParikhTestHelpers {
  def compareFormulae(
      automaton: BricsAutomaton,
      newImage: Formula,
      oldImage: Formula
  ): Unit = {
    import ap.{PresburgerTools, SimpleAPI}
    import ap.parser.IConstant
    import ap.terfor.conjunctions.Conjunction

    SimpleAPI.withProver { p =>
      import p._
      automaton.registers.foreach {
        case IConstant(c) => addConstantRaw(c)
      }
      implicit val o = order
      val reduced =
        PresburgerTools.elimQuantifiersWithPreds(Conjunction.conj(oldImage, o))

      addConclusion(
        Conjunction.conj(newImage, o) <=>
          Conjunction.conj(reduced, o)
      )
      if (??? != SimpleAPI.ProverStatus.Valid) {
        println(
          s"simplified new image: ${pp(simplify(asIFormula(Conjunction.conj(newImage, o))))}"
        )
        println(s"simplified old image: ${pp(simplify(asIFormula(reduced)))}")

        assert(false, s"Countermodel: ${partialModel}")
      }

    }

  }

  implicit class SaneBuilder(builder: BricsAutomatonBuilder) {
    def getAutomatonWithRegisters(): BricsAutomaton = {
      val a = builder.getAutomaton
      a.addEtaMaps(builder.etaMap)
      if (!a.transitions.isEmpty) {
        a.addNewRegister(builder.etaMap(a.transitions.next).size)
      }
      a
    }

    def addNewStates(nr_state: Int): Array[BricsAutomaton#State] = {
      (0 to nr_state).map(_ => builder.getNewState).to[Array]
    }
  }

  val allChars: (Char, Char) = (0, 65535)

  val oneDotSmtFourStateAutomaton = {
    val builder = new BricsAutomatonBuilder
    val states = builder.addNewStates(4)
    states.foreach(builder.setAccept(_, true))
    builder.setInitialState(states(0))

    // Now we just need the transitions

    builder
      .addTransition(states(0), allChars, states(0), List(1, 1, 0, 0))
      .addTransition(states(0), (0, 66), states(1), List(0, 1, 0, 1))
      .addTransition(states(0), allChars, states(2), List(0, 1, 1, 1))
      .addTransition(states(0), (68, 65535), states(1), List(0, 1, 0, 1))

    builder
      .addTransition(states(1), (0, 66), states(1), List(0, 1, 0, 1))
      .addTransition(states(1), allChars, states(1), List(0, 1, 0, 0))
      .addTransition(states(1), allChars, states(3), List(0, 0, 0, 0))
      .addTransition(states(1), (68, 65535), states(1), List(0, 1, 0, 1))

    builder
      .addTransition(states(2), (0, 66), states(1), List(0, 1, 0, 1))
      .addTransition(states(2), allChars, states(2), List(0, 1, 1, 1))
      .addTransition(states(2), allChars, states(3), List(0, 0, 0, 0))
      .addTransition(states(2), (68, 65535), states(1), List(0, 1, 0, 1))

    builder.addTransition(states(3), allChars, states(3), List(0, 0, 0, 0))

    builder.getAutomatonWithRegisters
  }

}

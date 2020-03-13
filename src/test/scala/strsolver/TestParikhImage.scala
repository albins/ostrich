package strsolver

import org.scalatest.FunSuite
import org.scalatest.Assertions._
import strsolver.preprop.{BricsAutomaton, BricsAutomatonBuilder}
import ap.terfor.{Formula}

class TestParikhImage extends FunSuite {

  def compareFormulae(
      automaton: BricsAutomaton,
      newImage: Formula,
      oldImage: Formula
  ) = {
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

  test("1.smt2 partial countermodel bug") {
    val builder = new BricsAutomatonBuilder
    val states = (0 to 3)
      .map(_ => {
        val s = builder.getNewState;
        builder.setAccept(s, true);
        s
      })
      .to[Array]

    builder.setInitialState(states(0))

    // Now we just need the transitions

    builder.addTransition(states(0), (0, 65535), states(0), List(1, 1, 0, 0))
    builder.addTransition(states(0), (0, 66), states(1), List(0, 1, 0, 1))
    builder.addTransition(states(0), (0, 65535), states(2), List(0, 1, 1, 1))
    builder.addTransition(states(0), (68, 65535), states(1), List(0, 1, 0, 1))

    builder.addTransition(states(1), (0, 66), states(1), List(0, 1, 0, 1))
    builder.addTransition(states(1), (0, 65535), states(1), List(0, 1, 0, 0))
    builder.addTransition(states(1), (0, 65535), states(3), List(0, 0, 0, 0))
    builder.addTransition(states(1), (68, 65535), states(1), List(0, 1, 0, 1))

    builder.addTransition(states(2), (0, 66), states(1), List(0, 1, 0, 1))
    builder.addTransition(states(2), (0, 65535), states(2), List(0, 1, 1, 1))
    builder.addTransition(states(2), (0, 65535), states(3), List(0, 0, 0, 0))
    builder.addTransition(states(2), (68, 65535), states(1), List(0, 1, 0, 1))

    builder.addTransition(states(3), (0, 65535), states(3), List(0, 0, 0, 0))

    val automaton = builder.getAutomaton
    automaton.addEtaMaps(builder.etaMap)
    automaton.addNewRegister(4)
    println(automaton.toDot)

    val newImage = automaton.parikhImageNew
    val oldImage = automaton.parikhImageOld

    compareFormulae(automaton, newImage, oldImage)
  }
}

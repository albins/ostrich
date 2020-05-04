package strsolver

import org.scalatest.FunSuite
import strsolver.preprop.{BricsAutomaton, BricsAutomatonBuilder}

class TestParikhImage extends FunSuite {
  import ParikhTestHelpers.compareFormulae

  test("1.smt2 partial countermodel bug") {
    import ParikhTestHelpers.{oneDotSmtFourStateAutomaton => automaton}

    println(automaton.toDot)

    val newImage = automaton.parikhImageNew
    val oldImage = automaton.parikhImageOld

    compareFormulae(automaton, newImage, oldImage)
  }
}

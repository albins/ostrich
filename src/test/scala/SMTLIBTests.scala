package strsolver

import ap.DialogUtil.asString

import org.scalacheck.{Arbitrary, Gen, Properties}
import org.scalacheck.Prop._

object SMTLIBTests extends Properties("SMTLIBTests") {

  def expectResult[A](expResult: String)(computation: => A): Boolean = {
    val result = asString {
      Console.withErr(ap.CmdlMain.NullStream) {
        computation
      }
    }

    (result split "\n") contains expResult
  }

  def checkFile(
      filename: String,
      result: String,
      extractOpts: String*
  ): Boolean =
    expectResult(result) {
      SMTLIBMain.doMain(
        (List("+assert", "+useparikh", "-timeout=10", filename) ++ extractOpts).toArray
      )
    }

  property("length-1.smt2") =
    checkFile("tests/hu-benchmarks/length-1.smt2", "unsat")

  // We currently get a wrong answer for this test case: unsat instead of sat
  //  property("length-2.smt2") =
  //    checkFile("tests/hu-benchmarks/length-2.smt2", "sat")

  property("length-2b.smt2") =
    checkFile("tests/hu-benchmarks/length-2b.smt2", "sat")
  property("length-2c.smt2") =
    checkFile("tests/hu-benchmarks/length-2c.smt2", "unsat")

  property("indexof-1.smt2") =
    checkFile("tests/hu-benchmarks/indexof-1.smt2", "unsat")
  property("indexof-2.smt2") =
    checkFile("tests/hu-benchmarks/indexof-2.smt2", "unsat")

}

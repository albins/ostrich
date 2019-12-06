/*
 * This file is part of Sloth, an SMT solver for strings.
 * Copyright (C) 2017  Philipp Ruemmer, Petr Janku
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

package strsolver

import ap._
import ap.parser._
import ap.parameters.PreprocessingSettings
import ap.util.CmdlParser

import scala.collection.mutable.ArrayBuffer
import ap.theories.TheoryRegistry
import strsolver.preprop.RRFunsToTransducer

object SMTLIBMain {

  class MainException(msg: String) extends Exception(msg)
  object TimeoutException extends MainException("timeout")
  object StoppedException extends MainException("stopped")

  def doMain(args: Array[String]): Unit =
    try {
      val filenames = new ArrayBuffer[String]
      var timeout: Option[Long] = None
      var model = false
      var assertions = false

      for (str <- args) str match {
        case CmdlParser.ValueOpt("timeout", value) =>
          timeout = Some(value.toLong * 1000)
        case CmdlParser.ValueOpt("nuxmvtime", value) =>
          Flags.nuxmvTime = value
        case CmdlParser.Opt("model", value) =>
          model = value
        case CmdlParser.Opt("assert", value) =>
          assertions = value
        case CmdlParser.Opt("useparikh", _) =>
          Flags.useParikh = true
        case str =>
          filenames += str
      }

      if (filenames.size != 1)
        throw new Exception("expected a single filename as argument")

      val startTime = System.currentTimeMillis

      val timeoutChecker = timeout match {
        case Some(to) =>
          () => {
            if (System.currentTimeMillis - startTime > to)
              throw TimeoutException
          }
        case None => () =>
      }

      ap.util.Debug.enableAllAssertions(assertions)

      ////////////////////////////////////////////////////////////////////////////

      val fileName = filenames.head
//debug----------------
      Console.err.println("Reading file " + fileName + " ...")

      val reader = new SMTReader(fileName)
      val bitwidth = reader.bitwidth
      if (reader.includesGetModel)
        model = true

      // just handle the problem using a normal solver
      val functionEnc =
        new FunctionEncoder(true, false)
      for (t <- reader.signature.theories)
        functionEnc addTheory t

      val (List(INamedPart(_, formula)), _, signature) =
        Preprocessing(
          reader.rawFormula,
          List(),
          reader.signature,
          PreprocessingSettings.DEFAULT,
          functionEnc
        )

      // tell the AFA store about introduced relations
      for ((p, f) <- functionEnc.predTranslation)
        if ((TheoryRegistry lookupSymbol f).isEmpty) {
          RRFunsToTransducer.addRel2Fun(p, f)
        }

      val formulaWithoutQuans = SMTReader.eliminateUniQuantifiers(formula)
      val intFormula =
        StringTheoryTranslator(formulaWithoutQuans, reader.wordConstants)

      ap.util.Timer.reset
      val p = SimpleAPI
      SimpleAPI.withProver(enableAssert = assertions) { p =>
        import IExpression._
        import SimpleAPI._
        import p._
        import strsolver.preprop.AllocRegisterTerm
        // import strsolver.preprop.StoreLC

        try {
          addTheory(StringTheory)
          addConstantsRaw(SymbolCollector constantsSorted intFormula)
          addRelations(
            for (p <- signature.order.orderedPredicates.toSeq sortBy (_.name);
                 if ((TheoryRegistry lookupSymbol p).isEmpty))
              yield p
          )

          ??(intFormula)

//debug----------------
          Console.err.println
          val res = {
            checkSat(false)
            while (getStatus(100) == ProverStatus.Running) timeoutChecker()
            ???
          }
          res match {
            case ProverStatus.Valid        => println("unsat")
            case ProverStatus.Inconclusive => println("unknown")
            case ProverStatus.OutOfMemory  => println("OOM")
            case ProverStatus.Invalid => {
              println("sat")
            }
          }
          println("get time:")
          Console.err.println(ap.util.Timer)
        } finally {
          // Make sure that the prover actually stops. If stopping takes
          // too long, kill the whole process
          stop(false)
          if (getStatus(100) == ProverStatus.Running) {
            println("timeout")
            println("get time:")
            Console.err.println(ap.util.Timer)
            System exit 1
          }
        }
      }
    } catch {
      case t @ (TimeoutException) => {
        println("get time:")
        Console.err.println(ap.util.Timer)
        println("timeout")
        System exit 1
      }
      case t: Throwable => {
        println("(error \"" + t.getMessage + "\")")
        t.printStackTrace
        System exit 1
      }
    }

  def main(args: Array[String]): Unit = {
    doMain(args)
  }

}

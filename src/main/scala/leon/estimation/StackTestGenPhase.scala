package leon
package estimations

import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon.purescala.ScalaPrinter
import leon.utils._
import invariant.util._
import invariant.util.CallGraphUtil
import invariant.structure.FunctionUtils._
import scala.collection.mutable.{Map => MutableMap}

object StackTestGenPhase extends TransformationPhase {
  val name = "StackTestGenPhase"
  val description = "Generates a program to estimate real time stack usage of the input program"

  def apply(ctx: LeonContext, program: Program): Program = {
    val instprog = new StackTestGen(ctx, program)
    instprog.apply
  }
}

class StackTestGen(ctx: LeonContext, program: Program) {
  def apply = {
    val funcs =
      """
object ModularTests {
  import scala.util.control.Breaks._
  // Import the objects needed
  import ???

  // Hold the input
  var input: List = Nil()

  // This function generates the test input
  def genInput(inpSize: BigInt) = {
    ???
  }

  def setInput(n: BigInt) = {
    input = genInput(n)
  }

  def fillStack(n: BigInt): BigInt = {
    if (n == 0) {
      // Do not remove/add vals here. If that is needed, the constants below in main need to be re-estimated
      val empty = ???
      // Call the function to test here.
      return 0;
    }
    else {
      val m = fillStack(n - 1) + 1;
      return m;
    }
  }

  // Takes the size of the input as a command line argument
  def main(args: Array[String]) {
    val initIte = 8000         // May be reduced for faster convergence
    val jvmFixe = 105904
    val fillerSize = 112
    val jvmStackSize = 228      //Change this is needed

    var lowIte = 0
    var higIte = initIte

    setInput(Integer.parseInt(args(0)))

    while(true) {
      val midIte = (lowIte + higIte) / 2
      println("Filler Iterations: " + midIte)

      try {
        fillStack(midIte)
        lowIte = midIte
        if (higIte - lowIte <= 1) {
          println("Found: " + (jvmStackSize*1024 - jvmFixe - midIte*fillerSize))
          break
        }
      }
      catch {
        // FillerException. Reduce iterations
        case _: StackOverflowError => {
          println("fillerError");
          if (higIte - lowIte <= 1) {
            println("Found: " + (jvmStackSize*1024 - jvmFixe - (midIte - 1)*fillerSize))
            break
          }
          higIte = midIte
        }
      }
    }
  }
}
        """
    println(ScalaPrinter.apply(program) + "\n" + funcs)
    program
  }
}
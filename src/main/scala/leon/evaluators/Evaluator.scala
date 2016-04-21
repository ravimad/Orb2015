/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._

import solvers.Model

abstract class Evaluator(val context: LeonContext, val program: Program) extends LeonComponent {

  /** The type of value that this [[Evaluator]] calculates
    * Typically, it will be [[Expr]] for deterministic evaluators, and
    * [[Stream[Expr]]] for non-deterministic ones.
    */
  type Value

  type EvaluationResult = EvaluationResults.Result[Value]

  /** Evaluates an expression, using [[Model.mapping]] as a valuation function for the free variables. */
  def eval(expr: Expr, model: Model) : EvaluationResult

  /** Evaluates an expression given a simple model (assumes expr is quantifier-free).
    * Mainly useful for compatibility reasons.
    */
  final def eval(expr: Expr, mapping: Map[Identifier, Expr]) : EvaluationResult = eval(expr, new Model(mapping))

  /** Evaluates a ground expression. */
  final def eval(expr: Expr) : EvaluationResult = eval(expr, Model.empty)

  /** Compiles an expression into a function, where the arguments are the free variables in the expression.
    * `argorder` specifies in which order the arguments should be passed.
    * The default implementation uses the evaluation function each time, but evaluators are free
    * to (and encouraged to) apply any specialization.
    */
  def compile(expr: Expr, args: Seq[Identifier]) : Option[Model => EvaluationResult] = Some(
    (model: Model) => if(args.exists(arg => !model.isDefinedAt(arg))) {
      EvaluationResults.EvaluatorError("Wrong number of arguments for evaluation.")
    } else {
      eval (expr, model)
    }
  )
}

trait DeterministicEvaluator extends Evaluator {
  type Value = Expr
  
  /**Evaluates the environment first, resolving non-cyclic dependencies, and then evaluate the expression */
  final def evalEnvExpr(expr: Expr, mapping: Iterable[(Identifier, Expr)]) : EvaluationResult = {
    if(mapping.forall{ case (key, value) => purescala.ExprOps.isValue(value) }) {
      eval(expr, mapping.toMap)
    } else (evalEnv(mapping) match {
      case Left(m) => eval(expr, m)
      case Right(errorMessage) => 
        val m = mapping.filter{ case (k, v) => purescala.ExprOps.isValue(v) }.toMap
        eval(expr, m) match {
          case res @ evaluators.EvaluationResults.Successful(result) => res
          case _ => evaluators.EvaluationResults.EvaluatorError(errorMessage)
        }
    })
  }
  
  /** From a not yet well evaluated context with dependencies between variables, returns a head where all exprs are values (as a Left())
   *  If this does not succeed, it provides an error message as Right()*/
  private def evalEnv(mapping: Iterable[(Identifier, Expr)]): Either[Map[Identifier, Value], String] = {
    var f= mapping.toSet
    var mBuilder = collection.mutable.ListBuffer[(Identifier, Value)]()
    var changed = true
    while(f.nonEmpty && changed) {
      changed = false
      for((i, v) <- f) {
        eval(v, mBuilder.toMap).result match {
          case None =>
          case Some(e) =>
            changed = true
            mBuilder += ((i -> e))
            f -= ((i, v))
        }
      }
    }
    if(!changed) {
      val str = "In the context " + mapping + ",\n" +
      (for((i, v) <- f) yield {
        s"eval(${v}) returned the error: " + eval(v, mBuilder.toMap)
      }).mkString("\n")
      Right(str)
    } else Left(mBuilder.toMap)
  }
}

trait NDEvaluator extends Evaluator {
  type Value = Stream[Expr]
}

package leon
package invariant.templateSolvers

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import evaluators._
import java.io._
import solvers._
import solvers.combinators._
import solvers.smtlib._
import solvers.z3._
import scala.util.control.Breaks._
import purescala.ScalaPrinter
import scala.collection.mutable.{ Map => MutableMap }
import scala.reflect.runtime.universe
import invariant.engine._
import invariant.factories._
import invariant.util._
import invariant.util.ExpressionTransformer._
import invariant.structure._
import invariant.structure.FunctionUtils._
import Stats._

import Util._
import PredicateUtil._
import SolverUtil._

/**
 * This class uses Farkas' lemma to try and falsify numerical disjuncts with templates provided one by one
 */
class ExistentialQuantificationSolver(ctx: InferenceContext, program: Program) {
  import NLTemplateSolver._
  val reporter = ctx.reporter

  var currentCtr: Expr = tru
  private val farkasSolver = new FarkasLemmaSolver(ctx, program)

  def generateCtrsForUNSAT(lnctrs: Seq[LinearConstraint], temps: Seq[LinearTemplate]): Expr = {
    if (temps.isEmpty) {
      //here ants ^ conseq is sat (otherwise we wouldn't reach here) and there is no way to falsify this path
      fls
    } else farkasSolver.constraintsForUnsat(lnctrs, temps)
  }

  /**
   * Solves the nonlinear Farkas' constraints
   */
  def falsifySATDisjunct(newctrs: Seq[Expr], oldModel: Model): (Option[Boolean], Model) = {
    val newPart = createAnd(newctrs)
    val newSize = atomNum(newPart)
    val currSize = atomNum(currentCtr)

    Stats.updateCounterStats((newSize + currSize), "NLsize", "disjuncts")
    if (verbose) reporter.info("# of atomic predicates: " + newSize + " + " + currSize)

    val combCtr = And(currentCtr, newPart)
    val (res, newModel) = farkasSolver.solveFarkasConstraints(combCtr)
    res match {
      case _ if ctx.abort =>
        (None, Model.empty) // stop immediately
      case None =>
        //here we have timed out while solving the non-linear constraints
        if (verbose) reporter.info("NLsolver timed-out on the disjunct...")
        (None, Model.empty)
      case Some(false) =>
        currentCtr = fls
        (Some(false), Model.empty)
      case Some(true) =>
        currentCtr = combCtr
        //new model may not have mappings for all the template variables, hence, use the mappings from earlier models        
        (Some(true), completeWithRefModel(newModel, oldModel))
    }
  }
}

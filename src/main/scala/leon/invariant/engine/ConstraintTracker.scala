package leon
package invariant.engine

import purescala.Definitions._
import purescala.Expressions._
import invariant.structure._
import invariant.util.ExpressionTransformer._
import purescala.ExprOps._

class ConstraintTracker(ctx : InferenceContext, program: Program, rootFun : FunDef/*, temFactory: TemplateFactory*/) {

  //a mapping from functions to its VCs represented as a CNF formula
  protected var funcVCs = Map[FunDef,Formula]()

  val vcRefiner = new RefinementEngine(ctx, program, this)
  val specInstantiator = new SpecInstantiator(ctx, program, this)

  def getFuncs : Seq[FunDef] = funcVCs.keys.toSeq
  def hasVC(fdef: FunDef) = funcVCs.contains(fdef)
  def getVC(fd: FunDef) : Formula = funcVCs(fd)

  /**
   * @param body the body part of the VC that may possibly have instrumentation
   * @param specNeg Negation of the spec part e.g. pre ^ ~post that does not have instrumentation
   * The VC constructed is body ^ specNeg
   */
  def addVC(fd: FunDef, body: Expr, specNeg: Expr) = {
    val flatBody = normalizeExpr(body, ctx.multOp)
    val flatSpecNeg = normalizeExpr(specNeg, ctx.multOp)
    //println("flatBody: "+flatBody)
    //println("flatSpecNeg: "+flatSpecNeg)
    val specCalls = collect {
      case c @ Equals(_, _: FunctionInvocation) => Set[Expr](c)
      case _ => Set[Expr]()
    }(flatSpecNeg)
    val vc = And(flatBody, flatSpecNeg)
    funcVCs += (fd -> new Formula(fd, vc, ctx, specCalls))
  }

  def initialize = {
    //assume specifications
    specInstantiator.instantiate
  }

  def refineVCs(toUnrollCalls: Option[Set[Call]]) : Set[Call]  = {
    val unrolledCalls = vcRefiner.refineAbstraction(toUnrollCalls)
    specInstantiator.instantiate
    unrolledCalls
  }
}

/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package transformations

import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon.utils._
import leon.invariant.util.Util._

import scala.collection.mutable.{Map => MutableMap}

class TPRInstrumenter(p: Program, si: SerialInstrumenter) extends Instrumenter(p, si) {

  def costOf(e: Expr)(implicit fd: FunDef): Int = e match {
    case FunctionInvocation(fd, _) if !fd.hasBody => 0 // uninterpreted functions
    case FunctionInvocation(fd, args) => 1
    case t: Terminal => 0
    case _ => 1
  }

  def costOfExpr(e: Expr)(implicit fd: FunDef) = InfiniteIntegerLiteral(costOf(e))

  def inst = TPR

  val sccs = cg.sccs.flatMap { scc =>
    scc.map(fd => (fd -> scc.toSet))
  }.toMap

  //find all functions transitively called from rootFuncs (here ignore functions called via pre/post conditions)
  val (tprFuncs, tprTypes) = getRootFuncs()
  if (!tprTypes.isEmpty)
    throw new IllegalStateException("Higher-order functions are not supported by TPR instrumentation!")
  val timeFuncs = tprFuncs.foldLeft(Set[FunDef]())((acc, fd) => acc ++ cg.transitiveCallees(fd)).filter(_.hasBody)

  def functionsToInstrument(): Map[FunDef, List[Instrumentation]] = {
    var emap = MutableMap[FunDef,List[Instrumentation]]()
    def update(fd: FunDef, inst: Instrumentation) {
      if (emap.contains(fd))
        emap(fd) :+= inst
      else emap.update(fd, List(inst))
    }
    tprFuncs.map(fd => update(fd, TPR))
    timeFuncs.map(fd => update(fd, Time))
    emap.toMap
  }

  // TODO: ignoring applications. Fix this.
  def functionTypesToInstrument() =  Map()

  def additionalfunctionsToAdd() = Seq()

  def patternCost(pattern: Pattern, innerPat: Boolean, countLeafs: Boolean): Int = {
    pattern match {
      case InstanceOfPattern(_, _) => {
        if (innerPat) 2 else 1
      }
      case WildcardPattern(None) => 0
      case WildcardPattern(Some(id)) => {
        if (countLeafs && innerPat) 1
        else 0
      }
      case CaseClassPattern(_, _, subPatterns) => {
        (if (innerPat) 2 else 1) + subPatterns.foldLeft(0)((acc, subPat) =>
          acc + patternCost(subPat, true, countLeafs))
      }
      case TuplePattern(_, subPatterns) => {
        (if (innerPat) 2 else 1) + subPatterns.foldLeft(0)((acc, subPat) =>
          acc + patternCost(subPat, true, countLeafs))
      }
      case LiteralPattern(_, _) => if (innerPat) 2 else 1
      case _ =>
        throw new NotImplementedError(s"Pattern $pattern not handled yet!")
    }
  }

  def instrumentMatchCase(me: MatchExpr, mc: MatchCase, caseExprCost: Expr, scrutineeCost: Expr)(implicit fd: FunDef): Expr = {
    val costMatch = costOfExpr(me)
    val totalCostOfMatchPatterns = {
      me.cases.take(me.cases.indexOf(mc)).foldLeft(0)(
        (acc, currCase) => acc + patternCost(currCase.pattern, false, false)) +
        patternCost(mc.pattern, false, true)
    }
    Plus(costMatch, Plus(Plus(InfiniteIntegerLiteral(totalCostOfMatchPatterns), caseExprCost), scrutineeCost))
  }

  def instrument(e: Expr, subInsts: Seq[Expr], funInvResVar: Option[Variable] = None)
    (implicit fd: FunDef, letIdMap: Map[Identifier,Identifier]): Expr = e match {
    case t: Terminal => costOfExpr(t)
    case FunctionInvocation(tfd, args) => {
      val remSubInsts = if (tprFuncs.contains(tfd.fd))
        subInsts.slice(0, subInsts.length - 1)
      else subInsts
      if (sccs(fd)(tfd.fd)) {
        remSubInsts.foldLeft(costOfExpr(e) : Expr)(
          (acc: Expr, subeTime: Expr) => Plus(subeTime, acc))
      }
      else {
        val allSubInsts = remSubInsts :+ si.selectInst(tfd.fd)(funInvResVar.get, Time)
        allSubInsts.foldLeft(costOfExpr(e) : Expr)(
          (acc: Expr, subeTime: Expr) => Plus(subeTime, acc))
      }
    }
    case _ =>
      subInsts.foldLeft(costOfExpr(e) : Expr)(
        (acc: Expr, subeTime: Expr) => Plus(subeTime, acc))
  }

  def instrumentIfThenElseExpr(e: IfExpr, condInst: Option[Expr],
      thenInst: Option[Expr], elzeInst: Option[Expr])(implicit fd: FunDef): (Expr, Expr) = {
    val costIf = costOfExpr(e)
    (Plus(costIf, Plus(condInst.get, thenInst.get)),
      Plus(costIf, Plus(condInst.get, elzeInst.get)))
  }
}
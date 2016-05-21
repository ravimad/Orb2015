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
import invariant.util._
import Util._
import ProgramUtil._
import TypeUtil._

object timeCostModel {
  def costOf(e: Expr): Int = e match {
    case FunctionInvocation(fd, _) if !fd.hasBody => 0 // uninterpreted functions
    case FunctionInvocation(fd, args) => 1
    case t: Terminal => 0
    case _ => 1
  }

  def costOfExpr(e: Expr) = InfiniteIntegerLiteral(costOf(e))
}

class TimeInstrumenter(p: Program, si: SerialInstrumenter) extends Instrumenter(p, si) {
  import timeCostModel._

  def inst = Time

  val (funsToInst, funTypesToInst) = {    
    val funToFTypes = userLevelFunctions(p).map { fd => 
      def rec(e: Expr): Set[CompatibleType] = e match {     
        case NoTree(_) => Set()
        case l@Lambda(_, b) => rec(b) + new CompatibleType(l.getType)
        case Ensuring(b, Lambda(_, p)) => rec(b) ++ rec(p)
        case Operator(args, op) => args.toSet flatMap rec
      }      
      fd -> rec(fd.fullBody)
    }.toMap
    var instFuns = getRootFuncs()
    var newFuns = instFuns
    var instFunTypes = Set[CompatibleType]()
    while(!newFuns.isEmpty) {
      // (a) find all function types of applications in the nextSets
      val appTypes = newFuns flatMap {
        case ifd if ifd.hasBody =>
          collect[CompatibleType] {
            case Application(l, _) => Set(new CompatibleType(l.getType))
            case _ => Set()
          }(ifd.body.get)
        case _ => Set[CompatibleType]()
      }         
      // (b) find all userLevelFunctions that may create a lambda compatible with the types of the application.
      val newRoots = funToFTypes.collect { 
        case (fd, ftypes) if !ftypes.intersect(appTypes).isEmpty => fd        
      }
      // (c) find all functions transitively called from rootFuncs (here ignore functions called via pre/post conditions)
      val nextFunSet = newRoots.flatMap(cg.transitiveCallees).filter(_.hasBody).toSet // ignore uninterpreted functions
      newFuns = nextFunSet -- instFuns
      instFuns ++= nextFunSet      
      instFunTypes ++= appTypes
    }
    (instFuns, instFunTypes)
  }

  def functionsToInstrument(): Map[FunDef, List[Instrumentation]] = {
    //println("Root funs: "+getRootFuncs().map(_.id).mkString(",")+" All funcs: "+ instFunSet.map(_.id).mkString(","))
    funsToInst.map(x => (x, List(Time))).toMap
  }
  
  def functionTypesToInstrument(): Map[CompatibleType, List[Instrumentation]] = {
    funTypesToInst.map(x => (x, List(Time))).toMap
  }

  def additionalfunctionsToAdd() = Seq()

  /**
   * Computes the complete cost of match
   */
  def instrumentMatchCase(
    me: MatchExpr,
    mc: MatchCase,
    caseExprCost: Expr,
    scrutineeCost: Expr): Expr = {
    val costMatch = costOfExpr(me)

    def totalCostOfMatchPatterns(me: MatchExpr, mc: MatchCase): BigInt = {

      def patCostRecur(pattern: Pattern, innerPat: Boolean, countLeafs: Boolean): Int = {
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
              acc + patCostRecur(subPat, true, countLeafs))
          }
          case TuplePattern(_, subPatterns) => {
            (if (innerPat) 2 else 1) + subPatterns.foldLeft(0)((acc, subPat) =>
              acc + patCostRecur(subPat, true, countLeafs))
          }
          case LiteralPattern(_, _) => if (innerPat) 2 else 1
          case _ =>
            throw new NotImplementedError(s"Pattern $pattern not handled yet!")
        }
      }

      me.cases.take(me.cases.indexOf(mc)).foldLeft(0)(
        (acc, currCase) => acc + patCostRecur(currCase.pattern, false, false)) +
        patCostRecur(mc.pattern, false, true)
    }

    Plus(costMatch, Plus(
      Plus(InfiniteIntegerLiteral(totalCostOfMatchPatterns(me, mc)),
        caseExprCost),
      scrutineeCost))
  }

  def instrument(e: Expr, subInsts: Seq[Expr], funInvResVar: Option[Variable] = None)
  	(implicit fd: FunDef, letIdMap: Map[Identifier,Identifier]): Expr = e match {
    case t: Terminal => costOfExpr(t)
    case _ =>
      subInsts.foldLeft(costOfExpr(e) : Expr)(
        (acc: Expr, subeTime: Expr) => Plus(subeTime, acc))
  }

  /**
   * consInst Time taken by condition
   * thenInst - Time taken by then branch
   * @return values is a pair. 1st component is time when condition is tru, 2nd component
   * is time when condition is false.
   */
  def instrumentIfThenElseExpr(e: IfExpr, condInst: Option[Expr],
      thenInst: Option[Expr], elzeInst: Option[Expr]): (Expr, Expr) = {
    val costIf = costOfExpr(e)
    (Plus(costIf, Plus(condInst.get, thenInst.get)),
      Plus(costIf, Plus(condInst.get, elzeInst.get)))
  }
}
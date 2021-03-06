/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package termination

import purescala.Definitions._
import scala.collection.mutable.{ Map => MutableMap }
import purescala.Expressions._
import purescala.Common._
import scala.concurrent.duration._
import leon.solvers._
import purescala.ExprOps._
import purescala.TypeOps.instantiateType
import purescala.ScalaPrinter
import purescala.Path
import purescala.SelfPrettyPrinter
import purescala.PrettyPrinter
import purescala.Constructors._
import purescala.Types._
import laziness.HOMemUtil._
import scala.annotation.tailrec

/**
 * Checks terminations of functions using the ranking function specified in the `decreases`
 * construct. For now, it works only on first-order functions.
 */

class DecreasesProcessor(val checker: TerminationChecker) extends Processor {

  val name: String = "Decreases Processor"

  private val solver: SolverFactory[Solver] = {
    val solfac = SolverFactory.getFromSettings(checker.context, checker.program)
    checker.context.findOption(GlobalOptions.optTimeout) match {
      case Some(timeout) => solfac.withTimeout(timeout)
      case _             => solfac
    }
  }

  private val zero = InfiniteIntegerLiteral(0)
  private val tru = BooleanLiteral(true)

  val p = checker.program

  /**
   * Check that there are no visible functions using application.
   * Note: creating lambdas without using them is harmless. They are just like
   * data structure creation.
   */
  /*private val hasClosures = checker.functions.filterNot(_.annotations contains "library").exists { fd =>
    Seq(fd.fullBody, fd.decreaseMeasure.getOrElse(tru)).exists(exists {
      case app: Application => true
      case _                => false
    } _)
  }*/

  sealed abstract class FailReason(funDef: FunDef)
  case class TryOther(funDef: FunDef) extends FailReason(funDef)
  case class FailStop(funDef: FunDef) extends FailReason(funDef)

   // TODO: Should we remove cached predicate before giving it to the solver ?
  def run(problem: Problem): Option[Seq[Result]] = {
    val fds = problem.funDefs
    println("Sccs: "+checker.program.callGraph.stronglyConnectedComponents.find(_.contains(fds.head)).get.map(_.id))
    if (fds.exists { _.decreaseMeasure.isDefined }) {
      /*if (hasClosures) {
        reporter.error("Cannot use `decreases` in the presence of first-class functions")
        return None
      }*/
      // Important:
      // Here, we filter only functions that have a measure. This is sound because of the following reasoning.
      // Functions in the scc that do not have a decrease measure either will be inlined if it is not self recursive.
      // Otherwise, the caller of this function will carry the blame of non-termination.
      val fails: Seq[FailReason] = fds.filter(_.hasMeasure).flatMap { fd =>
        val measure = fd.decreaseMeasure.get
        reporter.info(s"- Now considering `decreases` of ${fd.id.name} @${fd.id.getPos}...")
        // (a) check if every function in the measure terminates and does not make a recursive call to an SCC.
        if (exists {
          case FunctionInvocation(TypedFunDef(decCallee, _), _) if checker.functions(decCallee) =>
            if (problem.funSet(decCallee)) {
              reporter.warning(s"==> INVALID: `decreases` has recursive call to ${decCallee.id.name}.")
              true
            } else if (!checker.terminates(decCallee).isGuaranteed) {
              reporter.warning(s"==> INVALID: `decreases` calls non-terminating function ${decCallee.id.name}.")
              true
            } else false
          case _ =>
            false
        }(measure)) {
          Seq(FailStop(fd))
        } else {
          // (b) check if the measure is well-founded
          val nonneg = measure.getType match {
            case TupleType(tps) =>
              And((1 to tps.size).map(i => GreaterEquals(TupleSelect(measure, i), zero)))
            case _ =>
              GreaterEquals(measure, zero)
          }
          SimpleSolverAPI(solver).solveSAT(Not(nonneg)) match {
            case (Some(false), _) =>
              //(c) check if the measure decreases for recursive calls
              // remove certain function invocations from the body
              val recCallsWithPath = collectRecursiveCallsWithPaths(fd.fullBody, problem.funSet, Path.empty)
              val decRes = recCallsWithPath.foldLeft(None: Option[FailReason]) {
                case (acc @ Some(_), _) => acc
                case (acc, (fi @ FunctionInvocation(TypedFunDef(callee, tps), args), path)) =>
                  if (!callee.hasMeasure) {
                    // here, we cannot prove termination of the function as it calls a self-recursive function
                    // without a measure.
                    Some(TryOther(fd))
                  } else {
                    val calleeMeasure = callee.decreaseMeasure.get
                    val tparamMap = (callee.typeArgs zip tps).toMap
                    val paramMap = (callee.params.map(_.id.toVariable) zip args).toMap[Expr, Expr]
                    val callMeasure = instantiateType(replace(paramMap, freshenLocals(calleeMeasure)),
                      tparamMap, Map())
                    if (callMeasure.getType != measure.getType) {
                      reporter.warning(s" ==> INVALID: recursive call ${ScalaPrinter(fi)} uses a different measure type")
                      Some(TryOther(fd))
                    } else {
                      // construct a lexicographic less than check
                      val lessPred = measure.getType match {
                        case TupleType(tps) =>
                          val s = tps.size
                          (1 until s).foldRight(GreaterThan(TupleSelect(measure, s), TupleSelect(callMeasure, s)): Expr) {
                            (i, acc) =>
                              val m1 = TupleSelect(measure, i)
                              val m2 = TupleSelect(callMeasure, i)
                              Or(GreaterThan(m1, m2), And(Equals(m1, m2), acc))
                          }
                        case _ =>
                          GreaterThan(measure, callMeasure)
                      }
                      SimpleSolverAPI(solver).solveSAT(and(path.toPath, Not(lessPred))) match {
                        case (Some(false), _) => None
                        case (Some(true), model) =>
                          reporter.warning(s" ==> INVALID: measure doesn't decrease for the (transitive) call ${ScalaPrinter(fi)}")
                          printCounterExample(model)
                          Some(TryOther(fd))
                        case _ =>
                          reporter.warning(s"==> UNKNOWN: measure cannot be shown to decrease for (transitive) call ${ScalaPrinter(fi)}")
                          Some(TryOther(fd))
                      }
                    }
                  }
              }
              if (decRes.isEmpty)
                reporter.info(s"==> VALID")
              decRes.toSeq

            case (Some(true), model) =>
              reporter.warning(s" ==> INVALID: measure is not well-founded")
              printCounterExample(model)
              Seq(TryOther(fd))

            case _ =>
              reporter.warning(s"==> UNKNOWN: measure cannot be proven to be well-founded")
              Seq(TryOther(fd))
          }
        }
      }
      if (fails.isEmpty) {
        Some(fds.map(Cleared))
      } else if (fails.exists(_.isInstanceOf[FailStop])) {
        //reporter.warning(s"Termiantion failed for SCC: ${fds.map(_.id.name).mkString(",")}")
        Some(fds.map(Broken(_, Seq())))
      } else
        None
    } else
      None
  }

  /**
   * This method collects all recusive calls with paths. In case the
   * call does not have decrease measure, it inlines the body if it is not self-recusive,
   * and collects the path in the inlined version.
   */
  def collectRecursiveCallsWithPaths(rootExpr: Expr, scc: Set[FunDef], initPath: Path): Seq[(FunctionInvocation, Path)] = {
    val recCallsWithPath = CollectorWithPaths {
      case fi @ FunctionInvocation(TypedFunDef(callee, _), args) if scc(callee) =>
        fi
    } traverse (rootExpr, initPath)
    recCallsWithPath flatMap {
      case cp @ (FunctionInvocation(TypedFunDef(callee, _), _), _) if callee.hasMeasure =>
        Seq(cp)
      case cp @ (FunctionInvocation(TypedFunDef(callee, _), _), _) if checker.program.callGraph.calls(callee, callee) =>
        // here the recursive call does not have a measure, and the callee is also self recursive
        // we cannot do much but to fail (failure will be handled by the caller)
        reporter.warning(s"${callee.id} doesn't specify a measure and is self-recursive, while other functions in its SCC do: ${scc.map(_.id).mkString(",")}")
        Seq(cp)
      case (fi @ FunctionInvocation(TypedFunDef(callee, tps), args), path) =>
        // here the recursive call does not have a measure but is not self recursive
        // inline the recursive call and get the path to the recursive calls in the body
        val tparamMap = (callee.typeArgs zip tps).toMap
        val paramMap = (callee.params.map(_.id.toVariable) zip args).toMap[Expr, Expr]
        val inlinedBody = instantiateType(replace(paramMap, freshenLocals(callee.fullBody)), tparamMap, Map())
        collectRecursiveCallsWithPaths(inlinedBody, scc, path)
    }
  }

  def printCounterExample(model: Model) {
    // We use PrettyPrinter explicitly and not ScalaPrinter: printing very
    // large arrays faithfully in ScalaPrinter is hard, while PrettyPrinter
    // is free to simplify
    val strings = model.toSeq.sortBy(_._1.name).map {
      case (id, v) =>
        (id.asString(checker.context), SelfPrettyPrinter.print(v, PrettyPrinter(v))(checker.context, checker.program))
    }
    if (strings.nonEmpty) {
      val max = strings.map(_._1.length).max
      for ((id, v) <- strings) {
        reporter.warning(("  %-" + max + "s -> %s").format(id, v))
      }
    } else {
      reporter.warning(f"  (Empty counter-example)")
    }
  }
}

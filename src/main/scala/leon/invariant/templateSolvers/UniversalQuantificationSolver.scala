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

class UniversalQuantificationSolver(ctx: InferenceContext, program: Program,
                                    funs: Seq[FunDef], ctrTracker: ConstraintTracker,
                                    minimizer: Option[(Expr, Model) => Model]) {

  import NLTemplateSolver._

  //flags controlling debugging
  val debugUnflattening = false
  val debugIncrementalVC = false
  val trackCompressedVCCTime = false

  val printCounterExample = false
  val dumpInstantiatedVC = false

  val reporter = ctx.reporter
  val timeout = ctx.vcTimeout
  val leonctx = ctx.leonContext

  //flag controlling behavior  
  private val startFromEarlierModel = true
  val disableCegis = true
  private val useIncrementalSolvingForVCs = true
  private val usePortfolio = false // portfolio has a bug in incremental solving

  val defaultEval = new DefaultEvaluator(leonctx, program) // an evaluator for extracting models
  val existSolver = new ExistentialQuantificationSolver(ctx, program)
  val disjunctChooser = new DisjunctChooser(ctx, program, ctrTracker, defaultEval)

  val solverFactory =
    if (usePortfolio) {
      if (useIncrementalSolvingForVCs)
        throw new IllegalArgumentException("Cannot perform incremental solving with portfolio solvers!")
      SolverFactory(() => new PortfolioSolver(leonctx, Seq(new SMTLIBCVC4Solver(leonctx, program),
        new SMTLIBZ3Solver(leonctx, program))) with TimeoutSolver)
    } else
      SolverFactory.uninterpreted(leonctx, program)

  def splitVC(fd: FunDef) = {
    val (paramPart, rest, modCons) =
      time { ctrTracker.getVC(fd).toUnflatExpr } {
        t => Stats.updateCounterTime(t, "UnflatTime", "VC-refinement")
      }
    if (ctx.usereals) {
      (IntLiteralToReal(paramPart), IntLiteralToReal(rest), modCons)
    } else (paramPart, rest, modCons)
  }

  case class FunData(vcSolver: Solver with TimeoutSolver, modelCons: (Model, DefaultEvaluator) => FlatModel,
                     paramParts: Expr, simpleParts: Expr)
  val funInfos =
    if (useIncrementalSolvingForVCs) {
      funs.foldLeft(Map[FunDef, FunData]()) {
        case (acc, fd) =>
          val (paramPart, rest, modelCons) = splitVC(fd)
          if (hasReals(rest) && hasInts(rest))
            throw new IllegalStateException("Non-param Part has both integers and reals: " + rest)
          if (debugIncrementalVC) {
            assert(getTemplateVars(rest).isEmpty)
            println("For function: " + fd.id)
            println("Param part: " + paramPart)
          }
          if (!ctx.abort) { // this is required to ensure that solvers are not created after interrupts
            val vcSolver = solverFactory.getNewSolver()
            vcSolver.assertCnstr(rest)
            acc + (fd -> FunData(vcSolver, modelCons, paramPart, rest))
          } else acc
      }
    } else Map[FunDef, FunData]()

  def free = {
    if (useIncrementalSolvingForVCs)
      funInfos.foreach(entry => entry._2.vcSolver.free)
  }

  /**
   * State for minimization
   */
  class MinimizationInfo {
    var minStarted = false
    var minimized = false
    var lastCorrectModel: Option[Model] = None
    var minStartTime: Long = 0 // for stats

    def reset() = {
      minStarted = false
      lastCorrectModel = None
    }

    def updateProgress(model: Model) {
      lastCorrectModel = Some(model)
      if (!minStarted) {
        minStarted = true
        minStartTime = System.currentTimeMillis()
      }
    }

    def stop {
      reset()
      /*val mintime = (System.currentTimeMillis() - minStartTime)
      Stats.updateCounterTime(mintime, "minimization-time", "procs")
    	Stats.updateCumTime(mintime, "Total-Min-Time")*/
    }

    def getLastCorrectModel = lastCorrectModel
  }

  /**
   * State for recording diffcult paths
   */
  class DifficultPaths {
    var paths = MutableMap[FunDef, Seq[Expr]]()

    def addPath(fd: FunDef, cePath: Expr): Unit = {
      if (paths.contains(fd)) {
        paths.update(fd, cePath +: paths(fd))
      } else {
        paths += (fd -> Seq(cePath))
      }
    }
    def get(fd: FunDef) = paths.get(fd)
    def hasPath(fd: FunDef) = paths.contains(fd)
    def pathsToExpr(fd: FunDef) = Not(createOr(paths(fd)))
    def size = paths.values.map(_.size).sum
  }
  
  class ModelRefiner(tempModel: Model) {    
    val seenPaths = new DifficultPaths()
    val tempVarMap: Map[Expr, Expr] = tempModel.map { case (k, v) => (k.toVariable -> v) }.toMap
      var blockedCEs = false
      var conflictingFuns = funs.toSet
      var callsInPaths = Set[Call]()
      
    def nextCandidate() = { 
     var newConflicts = Set[FunDef]()
      val newctrsOpt = conflictingFuns.foldLeft(Some(Seq()): Option[Seq[Expr]]) {
        case (None, _) => None
        case (Some(acc), fd) =>
          val disabledPaths =
            if (seenPaths.hasPath(fd)) {
              blockedCEs = true
              seenPaths.pathsToExpr(fd)
            } else tru
          if (ctx.abort) None
          else {
            checkVCSAT(fd, tempModel, disabledPaths) match {
              case (None, _)        => None // VC cannot be decided
              case (Some(false), _) => Some(acc) // VC is unsat
              case (Some(true), univModel) => // VC is sat 
                newConflicts += fd
                if (verbose) reporter.info("Function: " + fd.id + "--Found candidate invariant is not a real invariant! ")
                if (printCounterExample) {
                  reporter.info("Model: " + univModel)
                }
                // chooose a sat numerical disjunct from the model
                val (lnctrs, temps, calls) =
                  time {
                    disjunctChooser.chooseNumericalDisjunct(ctrTracker.getVC(fd), univModel, tempModel.toMap)
                  } { chTime =>
                    updateCounterTime(chTime, "Disj-choosing-time", "disjuncts")
                    updateCumTime(chTime, "Total-Choose-Time")
                  }
                // generate constraints for making it unsat
                val farkasCtr = existSolver.generateCtrsForUNSAT(lnctrs, temps)
                if (farkasCtr == tru) throw new IllegalStateException("Cannot find a counter-example path!!")
                val disjunct = createAnd((lnctrs ++ temps).map(_.template))
                callsInPaths ++= calls
                //instantiate the disjunct
                val cePath = simplifyArithmetic(TemplateInstantiator.instantiate(disjunct, tempVarMap))
                //some sanity checks
                if (variablesOf(cePath).exists(TemplateIdFactory.IsTemplateIdentifier _))
                  throw new IllegalStateException("Found template identifier in counter-example disjunct: " + cePath)
                seenPaths.addPath(fd, cePath)
                Some(acc :+ farkasCtr)
            }
          }
      }
      newctrsOpt match {
        case None => // give up, the VC cannot be decided
          None
        case Some(newctrs) if (newctrs.isEmpty) =>
          conflictingFuns = newConflicts
          if (!blockedCEs) { //yes, hurray,found an inductive invariant                
            Some(false)
          } else {
            //give up, only hard paths remaining
            reporter.info("- Exhausted all easy paths !!")
            reporter.info("- Number of remaining hard paths: " + seenPaths.size)
            None //TODO: what to unroll here ?
          }
        case Some(newctrs) =>
          conflictingFuns = newConflicts
          existSolver.falsifySATDisjunct(newctrs, tempModel) match {
            case (None, _) =>
              //here we have timed out while solving the non-linear constraints
              if (verbose)
                reporter.info("NLsolver timed-out on the disjunct... blocking this disjunct...")
              Stats.updateCumStats(1, "retries")
              Some(true)
            case (Some(false), _) => // template not solvable, need more unrollings here    
              None
            case (Some(true), nextModel) =>              
              Some(true)

          }
      }
  }

  /**
   * Computes the invariant for all the procedures given a mapping for the
   * template variables.
   */
  def getAllInvariants(model: Model): Map[FunDef, Expr] = {
    val templates = ctrTracker.getFuncs.collect {
      case fd if fd.hasTemplate =>
        fd -> fd.getTemplate
    }
    TemplateInstantiator.getAllInvariants(model, templates.toMap)
  }

  def solveUNSAT(initModel: Model): (Option[Model], Option[Set[Call]]) = {
    val minimizationInfo = new MinimizationInfo()    
    var sat: Option[Boolean] = Some(true)
    var tempModel = initModel    
    var callsInPaths = Set[Call]()
    while (sat == Some(true) && !ctx.abort) {
      Stats.updateCounter(1, "disjuncts")
      if (verbose) {
        reporter.info("Candidate invariants")
        getAllInvariants(tempModel).foreach(entry => reporter.info(entry._1.id + "-->" + entry._2))
      }
      sat = 
    }
    sat match {
      case None => (None, Some(callsInPaths))
      case _ => (Some(tempModel), None)
    }    
  }
 

  //      res match {
  //        case _ if ctx.abort =>
  //          (None, None, model)
  //        case None if minStarted =>
  //          (Some(lastCorrectModel.get), None, model)
  //        case None =>
  //          //here, we cannot proceed and have to return unknown
  //          //However, we can return the calls that need to be unrolled
  //          (None, Some(seenCalls ++ newcalls), model)
  //        case Some(false) =>
  //          //here, the vcs are unsatisfiable when instantiated with the invariant
  //          if (minimizer.isDefined) {
  //            minimizationInProgress(model)
  //            if (minimized) {
  //              minimizationCompleted
  //              (Some(model), None, model)
  //            } else {
  //              val minModel = minimizer.get(inputCtr, model)
  //              minimized = true
  //              if (minModel == model) {
  //                minimizationCompleted
  //                (Some(model), None, model)
  //              } else {
  //                solveUNSAT(minModel, inputCtr, solvedDisjs, seenCalls)
  //              }
  //            }
  //          } else {
  //            (Some(model), None, model)
  //          }
  //        case Some(true) =>
  //          //here, we have found a new candidate invariant. Hence, the above process needs to be repeated
  //          minimized = false
  //          solveUNSAT(newModel, newCtr, solvedDisjs ++ newdisjs, seenCalls ++ newcalls)
  //      }
  //    }

  protected def instantiateTemplate(e: Expr, tempVarMap: Map[Expr, Expr]): Expr = {
    if (ctx.usereals) replace(tempVarMap, e)
    else
      simplifyArithmetic(TemplateInstantiator.instantiate(e, tempVarMap))
  }

  /**
   * Checks if the VC of fd is unsat
   */
  def checkVCSAT(fd: FunDef, tempModel: Model, disabledPaths: Expr): (Option[Boolean], LazyModel) = {
    val tempIdMap = tempModel.toMap
    val tempVarMap: Map[Expr, Expr] = tempIdMap.map { case (k, v) => k.toVariable -> v }.toMap
    val (solver, instExpr, modelCons) =
      if (useIncrementalSolvingForVCs) {
        val funData = funInfos(fd)
        val instParamPart = instantiateTemplate(funData.paramParts, tempVarMap)
        (funData.vcSolver, And(instParamPart, disabledPaths), funData.modelCons)
      } else {
        val (paramPart, rest, modCons) = ctrTracker.getVC(fd).toUnflatExpr
        val instPart = instantiateTemplate(paramPart, tempVarMap)
        (solverFactory.getNewSolver(), createAnd(Seq(rest, instPart, disabledPaths)), modCons)
      }
    //For debugging
    if (dumpInstantiatedVC) {
      val filename = "vcInst-" + FileCountGUID.getID
      val wr = new PrintWriter(new File(filename + ".txt"))
      val fullExpr =
        if (useIncrementalSolvingForVCs) {
          And(funInfos(fd).simpleParts, instExpr)
        } else instExpr
      wr.println("Function name: " + fd.id + " \nFormula expr: ")
      ExpressionTransformer.PrintWithIndentation(wr, fullExpr)
      wr.close()
    }
    if (debugUnflattening) {
      ctrTracker.getVC(fd).checkUnflattening(tempVarMap,
        SimpleSolverAPI(SolverFactory(() => solverFactory.getNewSolver())),
        defaultEval)
    }
    // sanity check
    if (hasMixedIntReals(instExpr))
      throw new IllegalStateException("Instantiated VC of " + fd.id + " contains mixed integer/reals: " + instExpr)
    //reporter.info("checking VC inst ...")
    solver.setTimeout(timeout * 1000)
    val (res, packedModel) =
      time {
        if (useIncrementalSolvingForVCs) {
          solver.push
          solver.assertCnstr(instExpr)
          val solRes = solver.check match {
            case _ if ctx.abort =>
              (None, Model.empty)
            case r @ Some(true) =>
              (r, solver.getModel)
            case r => (r, Model.empty)
          }
          solver.pop()
          solRes
        } else
          SimpleSolverAPI(SolverFactory(() => solver)).solveSAT(instExpr)
      } { vccTime =>
        if (verbose) reporter.info("checked VC inst... in " + vccTime / 1000.0 + "s")
        updateCounterTime(vccTime, "VC-check-time", "disjuncts")
        updateCumTime(vccTime, "TotalVCCTime")
      }
    //println("Packed model: "+packedModel.toMap)
    //for statistics
    if (trackCompressedVCCTime) {
      val compressedVC =
        unflatten(simplifyArithmetic(instantiateTemplate(ctrTracker.getVC(fd).eliminateBlockers, tempVarMap)))
      Stats.updateCounterStats(atomNum(compressedVC), "Compressed-VC-size", "disjuncts")
      time {
        SimpleSolverAPI(SolverFactory(() => solverFactory.getNewSolver())).solveSAT(compressedVC)
      } { compTime =>
        Stats.updateCumTime(compTime, "TotalCompressVCCTime")
        reporter.info("checked compressed VC... in " + compTime / 1000.0 + "s")
      }
    }
    (res, modelCons(packedModel, defaultEval))
  }
}

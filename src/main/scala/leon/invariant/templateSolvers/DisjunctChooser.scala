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

class DisjunctChooser(ctx: InferenceContext, program: Program, ctrTracker: ConstraintTracker, defaultEval: DefaultEvaluator) {
  val debugElimination = false
  val debugChooseDisjunct = false
  val debugTheoryReduction = false
  val debugAxioms = false
  val verifyInvariant = false
  val printPathToConsole = false
  val dumpPathAsSMTLIB = false

  val leonctx = ctx.leonContext
  val linearEval = new LinearRelationEvaluator(ctx) // an evaluator for quickly checking the result of linear predicates

  //additional book-keeping for statistics 
  val trackNumericalDisjuncts = false
  var numericalDisjuncts = List[Expr]()

  /**
   * A helper function used only in debugging.
   * TODO: this should also handle reals
   */
  protected def doesSatisfyExpr(expr: Expr, model: LazyModel): Boolean = {
    val compModel = variablesOf(expr).map { k => k -> model(k) }.toMap
    defaultEval.eval(expr, new Model(compModel)).result match {
      case Some(BooleanLiteral(true)) => true
      case _                          => false
    }
  }

  /**
   * This solver does not use any theories other than UF/ADT. It assumes that other theories are axiomatized in the VC.
   * This method can be overloaded by the subclasses.
   */
  protected def axiomsForTheory(formula: Formula, calls: Set[Call], model: LazyModel): Seq[Constraint] = Seq()

  /**
   * Chooses a purely numerical disjunct from a given formula that is
   * satisfied by the model
   * @precondition the formula is satisfied by the model
   * @tempIdMap a model for the template variables
   */
  protected def chooseNumericalDisjunct(formula: Formula, initModel: LazyModel, tempIdMap: Map[Identifier, Expr]): (Seq[LinearConstraint], Seq[LinearTemplate], Set[Call]) = {
    val satCtrs = formula.pickSatDisjunct(formula.firstRoot, initModel, tempIdMap, defaultEval) //this picks the satisfiable disjunct of the VC modulo axioms
    //for debugging
    if (debugChooseDisjunct || printPathToConsole || dumpPathAsSMTLIB || verifyInvariant) {
      val pathctrs = satCtrs.map(_.toExpr)
      val plainFormula = createAnd(pathctrs)
      val pathcond = simplifyArithmetic(plainFormula)
      if (debugChooseDisjunct) {
        satCtrs.filter(_.isInstanceOf[LinearConstraint]).map(_.toExpr).foreach((ctr) => {
          if (!doesSatisfyExpr(ctr, initModel))
            throw new IllegalStateException("Path ctr not satisfied by model: " + ctr)
        })
      }
      if (verifyInvariant) {
        println("checking invariant for path...")
        val sat = checkInvariant(pathcond, leonctx, program)
      }
      if (printPathToConsole) {
        //val simpcond = ExpressionTransformer.unFlatten(pathcond, variablesOf(pathcond).filterNot(TVarFactory.isTemporary _))
        val simpcond = pathcond
        println("Full-path: " + ScalaPrinter(simpcond))
        val filename = "full-path-" + FileCountGUID.getID + ".txt"
        val wr = new PrintWriter(new File(filename))
        ExpressionTransformer.PrintWithIndentation(wr, simpcond)
        println("Printed to file: " + filename)
        wr.flush()
        wr.close()
      }
      if (dumpPathAsSMTLIB) {
        val filename = "pathcond" + FileCountGUID.getID + ".smt2"
        toZ3SMTLIB(pathcond, filename, "QF_NIA", leonctx, program)
        println("Path dumped to: " + filename)
      }
    }
    var calls = Set[Call]()
    var adtExprs = Seq[Expr]()
    satCtrs.foreach {
      case t: Call                               => calls += t
      case t: ADTConstraint if (t.cons || t.sel) => adtExprs :+= t.expr
      // TODO: ignoring all set constraints here, fix this
      case _                                     => ;
    }
    val callExprs = calls.map(_.toExpr)

    val axiomCtrs = time {
      ctrTracker.specInstantiator.axiomsForCalls(formula, calls, initModel, tempIdMap, defaultEval)
    } { updateCumTime(_, "Total-AxiomChoose-Time") }

    //here, handle theory operations by reducing them to axioms.
    //Note: uninterpreted calls/ADTs are handled below as they are more general. Here, we handle
    //other theory axioms like: multiplication, sets, arrays, maps etc.
    val theoryCtrs = time {
      axiomsForTheory(formula, calls, initModel)
    } { updateCumTime(_, "Total-TheoryAxiomatization-Time") }

    //Finally, eliminate UF/ADT
    // convert all adt constraints to 'cons' ctrs, and expand the model
    val selTrans = new SelectorToCons()
    val cons = selTrans.selToCons(adtExprs)
    val expModel = selTrans.getModel(initModel)
    // get constraints for UFADTs
    val callCtrs = time {
      (new UFADTEliminator(leonctx, program)).constraintsForCalls((callExprs ++ cons),
        linearEval.predEval(expModel)).map(ConstraintUtil.createConstriant _)
    } { updateCumTime(_, "Total-ElimUF-Time") }

    //exclude guards, separate calls and cons from the rest
    var lnctrs = Set[LinearConstraint]()
    var temps = Set[LinearTemplate]()
    (satCtrs ++ callCtrs ++ axiomCtrs ++ theoryCtrs).foreach {
      case t: LinearConstraint => lnctrs += t
      case t: LinearTemplate   => temps += t
      case _                   => ;
    }
    if (debugChooseDisjunct) {
      lnctrs.map(_.toExpr).foreach((ctr) => {
        if (!doesSatisfyExpr(ctr, expModel))
          throw new IllegalStateException("Ctr not satisfied by model: " + ctr)
      })
    }
    if (debugTheoryReduction) {
      val simpPathCond = createAnd((lnctrs ++ temps).map(_.template).toSeq)
      if (verifyInvariant) {
        println("checking invariant for simp-path...")
        checkInvariant(simpPathCond, leonctx, program)
      }
    }
    if (trackNumericalDisjuncts) {
      numericalDisjuncts :+= createAnd((lnctrs ++ temps).map(_.template).toSeq)
    }
    val tempCtrs = temps.toSeq
    (eliminateVars(lnctrs.toSeq, tempCtrs), tempCtrs, calls)
  }

  /**
   * Endpoint of the pipeline. Invokes the Farkas Lemma constraint generation.
   * TODO:Remove transitive facts. E.g. a <= b, b <= c, a <=c can be simplified by dropping a <= c
   * TODO: simplify the formulas and remove implied conjuncts if possible (note the formula is satisfiable, so there can be no inconsistencies)
   * e.g, remove: a <= b if we have a = b or if a < b
   * Also, enrich the rules for quantifier elimination: try z3 quantifier elimination on variables that have an equality.
   * TODO: Use the dependence chains in the formulas to identify what to assertionize
   * and what can never be implied by solving for the templates
   */
  def eliminateVars(lnctrs: Seq[LinearConstraint], temps: Seq[LinearTemplate]): Seq[LinearConstraint] = {
    if (temps.isEmpty) lnctrs //here ants ^ conseq is sat (otherwise we wouldn't reach here) and there is no way to falsify this path
    else {
      if (debugElimination) {
        //println("Path Constraints (before elim): "+(lnctrs ++ temps))
        if (verifyInvariant) {
          println("checking invariant for disjunct before elimination...")
          checkInvariant(createAnd((lnctrs ++ temps).map(_.template)), leonctx, program)
        }
      }
      //compute variables to be eliminated
      val ctrVars = lnctrs.foldLeft(Set[Identifier]())((acc, lc) => acc ++ variablesOf(lc.toExpr))
      val tempVars = temps.foldLeft(Set[Identifier]())((acc, lt) => acc ++ variablesOf(lt.template))
      val elimVars = ctrVars.diff(tempVars)
      // for debugging
      val debugger =
        if (debugElimination && verifyInvariant) {
          Some((ctrs: Seq[LinearConstraint]) => {
            val debugRes = checkInvariant(createAnd((ctrs ++ temps).map(_.template)), leonctx, program)
          })
        } else None
      val elimLnctrs = time {
        LinearConstraintUtil.apply1PRuleOnDisjunct(lnctrs, elimVars, debugger)
      } { updateCumTime(_, "ElimTime") }

      if (debugElimination) {
        println("Path constriants (after elimination): " + elimLnctrs)
        if (verifyInvariant) {
          println("checking invariant for disjunct after elimination...")
          checkInvariant(createAnd((elimLnctrs ++ temps).map(_.template)), leonctx, program)
        }
      }
      //for stats
      if (ctx.dumpStats) {
        var elimCtrCount = 0
        var elimCtrs = Seq[LinearConstraint]()
        var elimRems = Set[Identifier]()
        elimLnctrs.foreach((lc) => {
          val evars = variablesOf(lc.toExpr).intersect(elimVars)
          if (evars.nonEmpty) {
            elimCtrs :+= lc
            elimCtrCount += 1
            elimRems ++= evars
          }
        })
        Stats.updateCounterStats((elimVars.size - elimRems.size), "Eliminated-Vars", "disjuncts")
        Stats.updateCounterStats((lnctrs.size - elimLnctrs.size), "Eliminated-Atoms", "disjuncts")
        Stats.updateCounterStats(temps.size, "Param-Atoms", "disjuncts")
        Stats.updateCounterStats(lnctrs.size, "NonParam-Atoms", "disjuncts")
      }
      elimLnctrs.distinct
    }
  }
}

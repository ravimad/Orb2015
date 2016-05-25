/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.util

import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import ProgramUtil._
import invariant.structure.FunctionUtils._
import invariant.datastructure._

/**
 * This represents a call graph of the functions in the program
 */
trait CallGraph extends Graph[FunDef] {
  lazy val reverseCG = reverse

  /*def addFunction(fd: FunDef) = graph.addNode(fd)

  def addEdgeIfNotPresent(src: FunDef, callee: FunDef): Unit = {
    if (!graph.containsEdge(src, callee))
      graph.addEdge(src, callee)
  }*/

  def callees(src: FunDef): Set[FunDef] = {
    successors(src)
  }

  def transitiveCallees(src: FunDef): Set[FunDef] = {
    BFSReachables(Seq(src))
  }

  def transitiveCallers(dest: FunDef) : Set[FunDef] = {
    BFSReachables(Seq(dest))
  }

  def transitiveCallees(srcs: Seq[FunDef]): Set[FunDef] = {
    BFSReachables(srcs)
  }

  def transitiveCallers(dests: Seq[FunDef]) : Set[FunDef] = {
    reverseCG.BFSReachables(dests)
  }

  def isRecursive(fd: FunDef): Boolean = {
    transitivelyCalls(fd, fd)
  }

  /**
   * Checks if the src transitively calls the procedure proc.
   * Note: We cannot say that src calls itself even though source is reachable from itself in the callgraph
   */
  def transitivelyCalls(src: FunDef, proc: FunDef): Boolean = {
    BFSReach(src, proc, excludeSrc = true)
  }

  def calls(src: FunDef, proc: FunDef): Boolean = {
    containsEdge(src, proc)
  }

  /**
   * Sorting functions in reverse topological order.
   * For functions within an SCC, we preserve the initial order
   * given as input
   */
  def reverseTopologicalOrder(initOrder: Seq[FunDef]): Seq[FunDef] = {
    val orderMap = initOrder.zipWithIndex.toMap
    sccs.flatMap{scc => scc.sortWith((f1, f2) => orderMap(f1) <= orderMap(f2)) }
  }

  override def toString: String = {
    val procs = nodes
    procs.foldLeft("")((acc, proc) => {
      acc + proc.id + " --calls--> " +
        successors(proc).foldLeft("")((acc, succ) => acc + "," + succ.id) + "\n"
    })
  }
}

object CallGraphUtil {

  /*def constructCallGraph(prog: Program,
      onlyBody: Boolean = false,
      withTemplates: Boolean = false,
      calleesFun: Expr => Set[FunDef] = getCallees): CallGraph = {
    val cg = new CallGraph()
    functionsWOFields(prog.definedFunctions).foreach{fd =>
      cg.addFunction(fd)
      if (fd.hasBody) {
        var funExpr = fd.body.get
        if (!onlyBody) {
          if (fd.hasPrecondition)
            funExpr = Tuple(Seq(funExpr, fd.precondition.get))
          if (fd.hasPostcondition)
            funExpr = Tuple(Seq(funExpr, fd.postcondition.get))
        }
        if (withTemplates && fd.hasTemplate) {
          funExpr = Tuple(Seq(funExpr, fd.getTemplate))
        }
        //introduce a new edge for every callee
        calleesFun(funExpr).foreach(cg.addEdgeIfNotPresent(fd, _))
      }
    }
    cg
  }*/

  def constructCallGraph(prog: Program, onlyBody: Boolean = false, withTemplates: Boolean = false): CallGraph = {
    val cg = new DirectedGraph[FunDef] with CallGraph { }
    functionsWOFields(prog.definedFunctions).foreach{fd =>
      cg.addNode(fd)
      if (fd.hasBody) {
        var funExpr = fd.body.get
        if (!onlyBody) {
          if (fd.hasPrecondition)
            funExpr = Tuple(Seq(funExpr, fd.precondition.get))
          if (fd.hasPostcondition)
            funExpr = Tuple(Seq(funExpr, fd.postcondition.get))
        }
        if (withTemplates && fd.hasTemplate) {
          funExpr = Tuple(Seq(funExpr, fd.getTemplate))
        }
        //introduce a new edge for every callee
        val callees = getCallees(funExpr)        
        callees.foreach{ce => cg.addEdge(fd, ce)}
      }
    }
    cg
  }

  def getCallees(expr: Expr): Set[FunDef] = collect {
    case expr@FunctionInvocation(TypedFunDef(callee, _), _) 
      if !callee.flags.contains(IsField(false)) =>
      Set(callee)
    case _ =>
      Set[FunDef]()
  }(expr)
}
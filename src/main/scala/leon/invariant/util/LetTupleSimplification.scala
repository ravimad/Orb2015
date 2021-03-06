/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.util

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import java.io._
import java.io._
import purescala.ScalaPrinter
import leon.utils._
import PredicateUtil._
import invariant.structure.Call
import invariant.structure.FunctionUtils._
import leon.transformations.InstUtil._
import TVarFactory._

/**
 * A collection of transformation on expressions and some utility methods.
 * These operations are mostly semantic preserving (specific assumptions/requirements are specified on the operations)
 */
object LetTupleSimplification {

  val zero = InfiniteIntegerLiteral(0)
  val one = InfiniteIntegerLiteral(1)
  val mone = InfiniteIntegerLiteral(-1)
  val tru = BooleanLiteral(true)
  val fls = BooleanLiteral(false)
  val bone = BigInt(1)
  // fresh ids created during simplification
  val simpContext = newContext

  def letSanityChecks(ine: Expr) = {
    simplePostTransform(_ match {
      case letExpr @ Let(binderId, letValue, body) if (binderId.getType != letValue.getType) =>
        throw new IllegalStateException("Binder and value type mismatch: " +
          s"(${binderId.getType},${letValue.getType})")
      case e => e
    })(ine)
  }

  /**
   * TODO: rewrite this function in a better way
   * This function simplifies lets of the form <Var> = <TupleType Expr> by replacing
   * uses of the <Var>._i by the approppriate expression in the let body or by
   * introducing a new let <Var'> = <Var>._i and using <Var'> in place of <Var>._i
   * in the original let body.
   * Caution: this function may not be idempotent.
   */
  def simplifyTuples(ine: Expr): Expr = {

    var processedLetBinders = Set[Identifier]()
    def recSimplify(e: Expr, replaceMap: Map[Expr, Expr]): Expr = {

      //println("Before: "+e)
      val transe = e match {
        case letExpr @ Let(binderId, letValue, body) if !processedLetBinders(binderId) =>
          processedLetBinders += binderId
          // transform the 'letValue' with the current map
          val nvalue = recSimplify(letValue, replaceMap)
          // enrich the map if letValue is of tuple type
          nvalue.getType match {
            case TupleType(argTypes) =>
              var freshBinders = Set[Identifier]()
              def freshBinder(typ: TypeTree) = {
                val freshid = createTemp(binderId.name, typ, simpContext)
                freshBinders += freshid
                freshid.toVariable
              }
              val newmap: Map[Expr, Expr] = nvalue match {
                case Tuple(args) => // this is an optimization for the case where nvalue is a tuple
                  args.zipWithIndex.map {
                    case (t: Terminal, index) =>
                      (TupleSelect(binderId.toVariable, index + 1) -> t)
                    case (_, index) =>
                      (TupleSelect(binderId.toVariable, index + 1) -> freshBinder(argTypes(index)))
                  }.toMap
                case _ =>
                  argTypes.zipWithIndex.map {
                    case (argtype, index) =>
                      (TupleSelect(binderId.toVariable, index + 1) -> freshBinder(argtype))
                  }.toMap
              }
              // transform the body using the new map + old map
              val nbody = recSimplify(body, replaceMap ++ newmap)
              val bodyFreevars = variablesOf(nbody)
              // create a sequence of lets for the freshBinders
              val nletBody = newmap.foldLeft(nbody) {
                case (acc, (k, Variable(id))) if freshBinders(id) && bodyFreevars(id) =>
                  // here, the 'id' is a newly created binder and is also used in the transformed body
                  Let(id, k, acc)
                case (acc, _) =>
                  acc
              }
              Let(binderId, nvalue, nletBody)
            case _ =>
              // no simplification can be done in this step
              Let(binderId, nvalue, recSimplify(body, replaceMap))
          }
        case ts @ TupleSelect(_, _) if replaceMap.contains(ts) =>
          postMap(replaceMap.lift, true)(e) //perform recursive replacements to handle nested tuple selects
        //replaceMap(ts) //replace tuple-selects in the map with the new identifier

        case ts @ TupleSelect(Tuple(subes), i) =>
          subes(i - 1)

        case t: Terminal => t

        case Operator(subes, op) =>
          op(subes.map(recSimplify(_, replaceMap)))
      }
      //println("After: "+e)
      transe
    }
    fixpoint((e: Expr) => simplifyArithmetic(recSimplify(e, Map())))(ine)
  }

  // sanity checks
  def checkTupleSelectInsideMax(e: Expr): Boolean = {
    //exists( predicate: Expr => Expr) (e)
    var error = false
    def helper(e: Expr): Unit = {
      e match {
        case FunctionInvocation(tfd, args) if (tfd.fd == maxFun) => {

          val Seq(arg1: Expr, arg2: Expr) = args
          (arg1, arg2) match {
            case (_: TupleSelect, _) => error = true
            case (_, _: TupleSelect) => error = true
            case _                   => { ; }
          }
        }

        case _ => { ; }
      }
    }

    postTraversal(helper)(e)
    error
  }

  def simplifyMax(ine: Expr): Expr = {
    val debugMaxSimplify = false
    //computes a lower bound value, assuming that every sub-term used in the term is positive
    //Note: this is applicable only to expressions involving depth
    def positiveTermLowerBound(e: Expr): Int = e match {
      case IntLiteral(v) => v
      case Plus(l, r)    => positiveTermLowerBound(l) + positiveTermLowerBound(r)
      case FunctionInvocation(tfd, args) if (tfd.fd == maxFun) => {
        val Seq(arg1, arg2) = args
        val lb1 = positiveTermLowerBound(arg1)
        val lb2 = positiveTermLowerBound(arg2)
        if (lb1 >= lb2) lb1 else lb2
      }
      case _ => 0 //other case are not handled as they do not appear
    }

    //checks if 'sub' is subsumed by 'e' i.e, 'e' will always take a value
    // greater than or equal to 'sub'.
    //Assuming that every sub-term used in the term is positive
    def subsumedBy(sub: Expr, e: Expr): Boolean = e match {
      case _ if (sub == e) => true
      case Plus(l, r)      => subsumedBy(sub, l) || subsumedBy(sub, r)
      case FunctionInvocation(tfd, args) if (tfd.fd == maxFun) =>
        val Seq(l, r) = args
        subsumedBy(sub, l) || subsumedBy(sub, r)
      case _ => false
    }

    // in the sequel, we are using the fact that 'depth' is positive and
    // 'ine' contains only 'depth' variables
    val simpe = simplePostTransform((e: Expr) => e match {
      case FunctionInvocation(tfd, args) if (tfd.fd == maxFun) => {
        if (debugMaxSimplify) {
          println("Simplifying: " + e)
        }
        val newargs: Seq[Expr] = args.map(simplifyArithmetic)
        val Seq(arg1: Expr, arg2: Expr) = newargs
        val simpval = if (!hasCalls(arg1) && !hasCalls(arg2)) {
          import invariant.structure.LinearConstraintUtil._
          val lt = exprToTemplate(LessEquals(Minus(arg1, arg2), InfiniteIntegerLiteral(0)))
          //now, check if all the variables in 'lt' have only positive coefficients
          val allPositive = lt.coeffTemplate.forall(entry => entry match {
            case (k, IntLiteral(v)) if (v >= 0) => true
            case _                              => false
          }) && (lt.constTemplate match {
            case None                            => true
            case Some(IntLiteral(v)) if (v >= 0) => true
            case _                               => false
          })
          if (allPositive) arg1
          else {
            val allNegative = lt.coeffTemplate.forall(entry => entry match {
              case (k, IntLiteral(v)) if (v <= 0) => true
              case _                              => false
            }) && (lt.constTemplate match {
              case None                            => true
              case Some(IntLiteral(v)) if (v <= 0) => true
              case _                               => false
            })
            if (allNegative) arg2
            else FunctionInvocation(tfd, newargs) //here we cannot do any simplification.
          }

        } else {
          (arg1, arg2) match {
            case (IntLiteral(v), r) if (v <= positiveTermLowerBound(r)) => r
            case (l, IntLiteral(v)) if (v <= positiveTermLowerBound(l)) => l
            case (l, r) if subsumedBy(l, r) => r
            case (l, r) if subsumedBy(r, l) => l
            case _ => FunctionInvocation(tfd, newargs)
          }
        }
        if (debugMaxSimplify) {
          println("Simplified value: " + simpval)
        }
        simpval
      }
      // case FunctionInvocation(tfd, args) if(tfd.fd.id.name == "max") => {
      // throw new IllegalStateException("Found just max in expression " + e + "\n")
      // }
      case _ => e
    })(ine)
    simpe
  }

  def inlineMax(ine: Expr): Expr = {
    //inline 'max' operations here
    simplePostTransform((e: Expr) => e match {
      case FunctionInvocation(tfd, args) if (tfd.fd == maxFun) =>
        val Seq(arg1, arg2) = args
        val bindWithLet = (value: Expr, body: (Expr with Terminal) => Expr) => {
          value match {
            case t: Terminal => body(t)
            case Let(id, v, b: Terminal) =>
              //here we can use 'b' in 'body'
              Let(id, v, body(b))
            case _ =>
              val mt = createTemp("mt", value.getType, simpContext)
              Let(mt, value, body(mt.toVariable))
          }
        }
        bindWithLet(arg1, a1 => bindWithLet(arg2, a2 =>
          IfExpr(GreaterEquals(a1, a2), a1, a2)))
      case _ => e
    })(ine)
  }

  def removeLetsFromLetValues(ine: Expr): Expr = {

    /**
     * Navigates through the sequence of lets in 'e'
     * and replaces its 'let' free part by subst.
     * Assuming that 'e' has only lets at the top and no nested lets in the value
     */
    def replaceLetBody(e: Expr, subst: Expr => Expr): Expr = e match {
      case Let(binder, letv, letb) =>
        Let(binder, letv, replaceLetBody(letb, subst))
      case _ =>
        subst(e)
    }

    // the function removes the lets from the let values
    // by pulling them out
    def pullLetToTop(e: Expr): Expr = {
      val transe = e match {
        case Lambda(args, body) =>
          Lambda(args, pullLetToTop(body))
        case Ensuring(body, pred) =>
          Ensuring(pullLetToTop(body), pullLetToTop(pred))
        case Require(pre, body) =>
          Require(pullLetToTop(pre), pullLetToTop(body))

        case letExpr @ Let(binder, letValue, body) =>
          // transform the 'letValue' with the current map
          pullLetToTop(letValue) match {
            case sublet @ Let(binder2, subvalue, subbody) =>
              // transforming "let v = (let v1 = e1 in e2) in e3"
              // to "let v1 = e1 in (let v = e2 in e3)"
              // here, subvalue is free of lets, but subbody may again be a let
              val newbody = replaceLetBody(subbody, Let(binder, _, pullLetToTop(body)))
              Let(binder2, subvalue, newbody)
            case nval =>
              // here, there is no let in the value
              Let(binder, nval, pullLetToTop(body))
          }

        //don't pull lets out of if-then-else branches and match cases
        case IfExpr(c, th, elze) =>
          replaceLetBody(pullLetToTop(c), IfExpr(_, pullLetToTop(th), pullLetToTop(elze)))

        case MatchExpr(scr, cases) =>
          val newcases = cases.map {
            case MatchCase(pat, guard, rhs) =>
              MatchCase(pat, guard map pullLetToTop, pullLetToTop(rhs))
          }
          replaceLetBody(pullLetToTop(scr), MatchExpr(_, newcases))

        case Operator(Seq(), op) =>
          op(Seq())

        case t: Terminal => t

        // handle And and Ors differently as they may short circuit like Ifs
        case And(args) => And(args map pullLetToTop)
        case Or(args) => Or(args map pullLetToTop)

        // Note: it is necessary to handle unary operators specially
        case Operator(Seq(sube), op) =>
          replaceLetBody(pullLetToTop(sube), e => op(Seq(e)))

        case Operator(subes, op) =>
          // transform all the sub-expressions
          val nsubes = subes map pullLetToTop
          //collects all the lets and makes the bodies a tuple
          var i = -1
          val transLet = nsubes.tail.foldLeft(nsubes.head) {
            case (acc, nsube) =>
              i += 1
              replaceLetBody(acc, e1 =>
                replaceLetBody(nsube, e2 => e1 match {
                  case _ if i == 0 =>
                    Tuple(Seq(e1, e2))
                  case Tuple(args) =>
                    Tuple(args :+ e2)
                }))
          }
          // TODO: using tuple here is dangerous it relies on  handling unary operators specially
          replaceLetBody(transLet, (e: Expr) => e match {
            case Tuple(args) =>
              op(args)
            case _ => op(Seq(e)) //here, there was only one argument
          })
      }
      // println(s"E : $e After Pulling lets to top : \n $transe")
      transe
    }
    val res = pullLetToTop(ine)
    /*if(debug)
      println(s"InE : $ine After Pulling lets to top : \n ${ScalaPrinter.apply(res)}")*/
    res
  }

  /**
   * Here, cntFun is assumed to be >= 0
   * The second return value is true if the cntFun was positive within a lambda.
   */
  def countWithLambda(cntFun: Expr => Int)(e: Expr): (Int, Boolean) = e match {
    case Lambda(_, lb) =>
      val (occ, withinLam) = countWithLambda(cntFun)(lb)
      if (occ > 0)
        (occ + cntFun(e), true)
      else
        (cntFun(e), withinLam)
    case Operator(args, op) =>
      args.foldLeft((cntFun(e), false)) {
        case ((occ, withinLam), arg) =>
          val (o, wl) = countWithLambda(cntFun)(arg)
          (occ + o, withinLam || wl)
      }
  }

  /**
   * This also preserves resources in the presence of higher-order functions
   */
  def simplerLet(ine: Expr): Expr = {
    def rec(t: Expr): Expr = {
      val res = t match {
        case letExpr @ Let(i, t: Terminal, b) =>
          replace(Map(Variable(i) -> t), b)

        // check if the let can be completely removed
        case letExpr @ Let(i, e, b) => {
          val (occurrences, withinLam) = countWithLambda {
            case Variable(x) if x == i => 1
            case _                     => 0
          }(b)
          if (occurrences == 0) {
            b
          } else if (occurrences == 1 && !withinLam) {
            replace(Map(Variable(i) -> e), b)
          } else {
            //TODO: we can also remove zero occurrences and compress the tuples
            // this may be necessary when instrumentations are combined.
            letExpr match {
              case letExpr @ Let(binder, lval @ Tuple(subes), b) =>
                def occurrences(index: Int) = {
                  countWithLambda {
                    case TupleSelect(sel, i) if sel == binder.toVariable && i == index => 1
                    case _ => 0
                  }(b)
                }
                val binderVar = binder.toVariable
                val repmap: Map[Expr, Expr] = subes.zipWithIndex.collect {
                  case (v @ Variable(_), i) => // sube is a variable ?
                    (TupleSelect(binderVar, i + 1) -> v)
                  case (ts @ TupleSelect(Variable(_), _), i) => // sube is a tuple select of a variable ?
                    (TupleSelect(binderVar, i + 1) -> ts)
                  case (sube, i) if occurrences(i + 1) == (1, false) => // sube is used only once ?
                    (TupleSelect(binderVar, i + 1) -> sube)
                }.toMap
                Let(binder, lval, replace(repmap, b))
              //note: here, we cannot remove the let,
              //if it is not used it will be removed in the next iteration
              case e => e
            }
          }
        }
        // also perform a tuple simplification
        case ts @ TupleSelect(Tuple(subes), i) =>
          subes(i - 1)
        // in the case of match or if-then-else or lets, push the tupleSelect into the cases or body
        case ts @ TupleSelect(sube, i) =>
          sube match {
            case MatchExpr(scr, cases) =>
              MatchExpr(scr, cases map {
                case MatchCase(pat, guard, body) =>
                  MatchCase(pat, guard, rec(TupleSelect(body, i)))
              })
            case IfExpr(cond, th, elze) =>
              IfExpr(cond, rec(TupleSelect(th, i)), rec(TupleSelect(elze, i)))
            case Let(id, v, b) =>
              Let(id, v, rec(TupleSelect(b, i)))
            case _ => ts
          }
        case e => e
      }
      res
    }
    fixpoint(simplePostTransform(rec))(ine)
  }

  def simplifyLetsAndLetsWithTuples(ine: Expr) = {

    val transforms = removeLetsFromLetValues _ andThen simplerLet _ andThen simplifyArithmetic
    transforms(ine)
  }

  /*
    This function tries to simplify a part of the expression tree consisting of the same operation.
    The operation needs to be associative and commutative for this simplification to work .
    Arguments:
      op: An implementation of the operation to be simplified
      getLeaves: Gets all the operands from the AST (if the argument is not of
                  the form currently being simplified, this is required to return an empty set)
      identity: The identity element for the operation
      makeTree: Makes an AST from the operands
  */
  def simplifyConstantsGeneral(e: Expr, op: (BigInt, BigInt) => BigInt,
                               getLeaves: (Expr, Boolean) => Seq[Expr], identity: BigInt,
                               makeTree: (Expr, Expr) => Expr): Expr = {

    val allLeaves = getLeaves(e, true)
    // Here the expression is not of the form we are currently simplifying
    if (allLeaves.size == 0) e
    else {
      // fold constants here
      val allConstantsOpped = allLeaves.foldLeft(identity)((acc, e) => e match {
        case InfiniteIntegerLiteral(x) => op(acc, x)
        case _                         => acc
      })

      val allNonConstants = allLeaves.filter((e) => e match {
        case _: InfiniteIntegerLiteral => false
        case _                         => true
      })

      // Reconstruct the expressin tree with the non-constants and the result of constant evaluation above
      if (allConstantsOpped != identity) {
        allNonConstants.foldLeft(InfiniteIntegerLiteral(allConstantsOpped): Expr)((acc: Expr, currExpr) => makeTree(acc, currExpr))
      } else {
        if (allNonConstants.size == 0) InfiniteIntegerLiteral(identity)
        else {
          allNonConstants.tail.foldLeft(allNonConstants.head)((acc: Expr, currExpr) => makeTree(acc, currExpr))
        }
      }
    }
  }

  //Use the above function to simplify additions and maximums interleaved
  def simplifyAdditionsAndMax(e: Expr): Expr = {
    def getAllSummands(e: Expr, isTopLevel: Boolean): Seq[Expr] = {
      e match {
        case Plus(e1, e2) => {
          getAllSummands(e1, false) ++ getAllSummands(e2, false)
        }
        case _ => if (isTopLevel) Seq[Expr]() else Seq[Expr](e)
      }
    }

    def getAllMaximands(e: Expr, isTopLevel: Boolean): Seq[Expr] = {
      e match {
        case FunctionInvocation(tfd, args) if (tfd.fd == maxFun) => {
          args.foldLeft(Seq[Expr]())((accSet, e) => accSet ++ getAllMaximands(e, false))
        }
        case _ => if (isTopLevel) Seq[Expr]() else Seq[Expr](e)
      }
    }

    simplePostTransform(e => {
      val plusSimplifiedExpr =
        simplifyConstantsGeneral(e, _ + _, getAllSummands, 0, ((e1, e2) => Plus(e1, e2)))

      // Maximum simplification assumes all arguments to max
      // are non-negative (and hence 0 is the identity)
      val maxSimplifiedExpr =
        simplifyConstantsGeneral(plusSimplifiedExpr,
          ((a: BigInt, b: BigInt) => if (a > b) a else b),
          getAllMaximands,
          0,
          ((e1, e2) => {
            val typedMaxFun = TypedFunDef(maxFun, Seq())
            FunctionInvocation(typedMaxFun, Seq(e1, e2))
          }))

      maxSimplifiedExpr
    })(e)
  }
}
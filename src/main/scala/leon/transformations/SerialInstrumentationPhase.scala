/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package transformations

import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon.purescala.ScalaPrinter
import leon.utils._
import invariant.util._
import Util._
import ProgramUtil._
import PredicateUtil._
import invariant.util.CallGraphUtil
import invariant.structure.FunctionUtils._
import scala.collection.mutable.{ Map => MutableMap, Set => MutableSet }

/**
 * An instrumentation phase that performs a sequence of instrumentations
 */

object InstrumentationPhase extends TransformationPhase {
  val name = "Instrumentation Phase"
  val description = "Instruments the program for all counters needed"

  def apply(ctx: LeonContext, program: Program): Program = {
    val si = new SerialInstrumenter(program)
    val instprog = si.apply
    //println("Instrumented Program: "+ScalaPrinter.apply(instprog, purescala.PrinterOptions(printUniqueIds = true)))
    instprog
  }
}

class SerialInstrumenter(program: Program,
                         exprInstOpt: Option[InstruContext => ExprInstrumenter] = None) {
  val debugInstrumentation = false

  val exprInstFactory = exprInstOpt.getOrElse((ictx: InstruContext) => new ExprInstrumenter(ictx))

  val instToInstrumenter: Map[Instrumentation, Instrumenter] =
    Map(Time -> new TimeInstrumenter(program, this),
      Depth -> new DepthInstrumenter(program, this),
      Rec -> new RecursionCountInstrumenter(program, this),
      Stack -> new StackSpaceInstrumenter(program, this),
      TPR -> new TPRInstrumenter(program, this))

  // a map from functions to the list of instrumentations to be performed for the function
  val (funcInsts, ftypeInsts) = {
    def update[T](fd: T, inst: Instrumentation, emap: MutableMap[T, List[Instrumentation]]) {
      if (emap.contains(fd))
        emap(fd) = (emap(fd) :+ inst).distinct
      else emap.update(fd, List(inst))
    }
    var fdmap = MutableMap[FunDef, List[Instrumentation]]()
    var ftypeMap = MutableMap[FunctionType, List[Instrumentation]]()

    instToInstrumenter.values.foreach { m =>
      m.functionsToInstrument.foreach({
        case (fd, instsToPerform) =>
          instsToPerform.foreach(instToPerform => update(fd, instToPerform, fdmap))
      })
      m.functionTypesToInstrument.foreach({
        case (ft, instsToPerform) =>
          instsToPerform.foreach(instToPerform => update(ft, instToPerform, ftypeMap))
      })
    }
    (fdmap.toMap, ftypeMap.toMap)
  }
  val instFuncs = funcInsts.keySet
  val instFuncTypes = ftypeInsts.keySet

  /**
   * Tracks the instrumentations necessary for a function type
   */
  def instsOfLambdaType(ft: FunctionType): Seq[Instrumentation] = ftypeInsts.getOrElse(ft, Seq())

  val adtsToInstrument = {
    Util.fix((adts: Set[ClassDef]) => {
      adts ++ program.definedClasses.collect {
        case cd: CaseClassDef if (cd.fields.map(_.getType).exists {
          case ft: FunctionType => instFuncTypes(ft)
          case ct: ClassType    => adts(ct.classDef)
          case _                => false
        }) =>
          cd.root
      }.toSet
    })(Set[ClassDef]())
  }

  val absTypeMap = adtsToInstrument.map {
    case adef @ AbstractClassDef(id, tparams, parent) =>
      adef -> new AbstractClassDef(FreshIdentifier(id.name, Untyped, true), tparams, parent)
    case cdef @ CaseClassDef(id, tparams, None, cobj) =>
      cdef -> new CaseClassDef(FreshIdentifier(id.name, Untyped, true), tparams, None, cobj)
  }.toMap[ClassDef, ClassDef]

  def fieldReplacementMap(fields: Seq[ValDef]) = {
    var fldMap = Map[TypeTree, TypeTree]()
    fields.map(_.getType).foreach {
      case ft @ FunctionType(argts, rett) =>
        val instTypes = instsOfLambdaType(ft).map(_.getType)
        if (!instTypes.isEmpty)
          fldMap += (ft -> FunctionType(argts, TupleType(rett +: instTypes)))
      case at: AbstractClassType if absTypeMap.contains(at.classDef) =>
        fldMap += (at -> AbstractClassType(absTypeMap(at.classDef).asInstanceOf[AbstractClassDef], at.tps))
      case ct: CaseClassType if absTypeMap.contains(ct.classDef) =>
        fldMap += (ct -> CaseClassType(absTypeMap(ct.classDef).asInstanceOf[CaseClassDef], ct.tps))
      case _ =>
    }
    fldMap
  }

  val adtSpecializer = new ADTSpecializer()
  /**
   * A map from old to new adts. The fields of the adts may have to be updated if they are of function types.
   */
  val adtMap = adtsToInstrument.flatMap {
    case absDef: AbstractClassDef =>
      val newTypeMap = absDef.typed.knownCCDescendants.flatMap { cc => fieldReplacementMap(cc.fields.toList) }.toMap
      val newDef = adtSpecializer.specialize(absDef, newTypeMap).asInstanceOf[AbstractClassDef]
      (absDef, newDef) +: (absDef.knownDescendants zip newDef.knownDescendants)

    case cdef: CaseClassDef if !cdef.parent.isDefined =>
      Seq((cdef, adtSpecializer.specialize(cdef, fieldReplacementMap(cdef.fields.toList))))
  }.toMap

  //create new functions. Augment the return type of a function iff the postcondition uses
  //the instrumentation variable or if the function is transitively called from such a function
  val funMap = (userLevelFunctions(program) ++ instFuncs).distinct.map { fd =>
    if (instFuncs.contains(fd)) {
      val newRetType = TupleType(fd.returnType +: funcInsts(fd).map(_.getType))
      // let the names of the function encode the kind of instrumentations performed
      val freshId = FreshIdentifier(fd.id.name + "-" + funcInsts(fd).map(_.name).mkString("-"), newRetType)
      (fd -> new FunDef(freshId, fd.tparams, fd.params, newRetType))
    } else {
      //here we need not augment the return types but do need to create a new copy
      (fd -> new FunDef(FreshIdentifier(fd.id.name, fd.returnType), fd.tparams, fd.params, fd.returnType))
    }
  }.toMap

  def instrumenters(fd: FunDef) = funcInsts(fd) map instToInstrumenter.apply _
  def instIndex(fd: FunDef)(ins: Instrumentation) = funcInsts(fd).indexOf(ins) + 2
  def selectInst(fd: FunDef)(e: Expr, ins: Instrumentation) = TupleSelect(e, instIndex(fd)(ins))

  def apply: Program = {

    if (instFuncs.isEmpty) program
    else {
      def mapExpr(ine: Expr): Expr = {
        simplePostTransform((e: Expr) => e match {
          case FunctionInvocation(tfd, args) if funMap.contains(tfd.fd) =>
            if (instFuncs.contains(tfd.fd))
              TupleSelect(FunctionInvocation(TypedFunDef(funMap(tfd.fd), tfd.tps), args), 1)
            else
              FunctionInvocation(TypedFunDef(funMap(tfd.fd), tfd.tps), args)
          case _ => e
        })(ine)
      }

      def mapBody(body: Expr, from: FunDef, to: FunDef) = {
        val res =
          if (from.isExtern) {
            // this is an extern function, we must only rely on the specs
            // so make the body empty
            NoTree(to.returnType)
          } else if (instFuncs.contains(from)) {
            val ictx = new InstruContext(from, this, funcInsts(from))
            exprInstFactory(ictx)(body)
          } else
            mapExpr(body)
        res
      }

      def mapPost(pred: Expr, from: FunDef, to: FunDef) = {
        pred match {
          case Lambda(Seq(ValDef(fromRes)), postCond) if (instFuncs.contains(from)) =>
            val toResId = FreshIdentifier(fromRes.name, to.returnType, true)
            val newpost = postMap((e: Expr) => e match {
              case Variable(`fromRes`) =>
                Some(TupleSelect(toResId.toVariable, 1))

              case _ if funcInsts(from).exists(_.isInstVariable(e)) =>
                val inst = funcInsts(from).find(_.isInstVariable(e)).get
                Some(TupleSelect(toResId.toVariable, instIndex(from)(inst)))

              case _ =>
                None
            })(postCond)
            Lambda(Seq(ValDef(toResId)), mapExpr(newpost))
          case _ =>
            mapExpr(pred)
        }
      }

      // Map the bodies and preconditions
      for ((from, to) <- funMap) {
        //copy annotations
        from.flags.foreach(to.addFlag(_))
        to.fullBody = from.fullBody match {
          case b @ NoTree(_) => NoTree(to.returnType)
          case Require(pre, body) =>
            //here 'from' does not have a postcondition but 'to' will always have a postcondition
            val toPost =
              Lambda(Seq(ValDef(FreshIdentifier("res", to.returnType))), BooleanLiteral(true))
            val bodyPre =
              Require(mapExpr(pre), mapBody(body, from, to))
            Ensuring(bodyPre, toPost)

          case Ensuring(Require(pre, body), post) =>
            Ensuring(Require(mapExpr(pre), mapBody(body, from, to)),
              mapPost(post, from, to))

          case Ensuring(body, post) =>
            Ensuring(mapBody(body, from, to), mapPost(post, from, to))

          case body =>
            val toPost =
              Lambda(Seq(ValDef(FreshIdentifier("res", to.returnType))), BooleanLiteral(true))
            Ensuring(mapBody(body, from, to), toPost)
        }
      }

      val additionalFuncs = funMap.flatMap {
        case (k, _) =>
          if (instFuncs(k))
            instrumenters(k).flatMap(_.additionalfunctionsToAdd)
          else List()
      }.toList.distinct

      val newprog = copyProgram(program, (defs: Seq[Definition]) =>
        defs.map {
          case fd: FunDef if funMap.contains(fd) =>
            funMap(fd)
          case d => d
        } ++ additionalFuncs)
      if (debugInstrumentation)
        println("After Instrumentation: \n" + ScalaPrinter.apply(newprog))

      ProgramSimplifier(newprog, instFuncs.toSeq)
    }
  }
}

/**
 * A set of paramteres that need to be passed around
 */
class InstruContext(
    val currFun: FunDef,
    val serialInst: SerialInstrumenter,
    val insts: Seq[Instrumentation],
    val enclLambda: Option[Lambda] = None) {

  val instrumenters = insts map serialInst.instToInstrumenter.apply _
  val instTypes = insts.map(_.getType)
  val funMap = serialInst.funMap
  val adtMap = serialInst.adtMap
  /**
   * Index of the instrumentation 'inst' in result tuple that would be created.
   * The return value will be >= 2 as the actual result value would be at index 1
   */
  def instIndex(ins: Instrumentation) = insts.indexOf(ins) + 2
  def selectInst(e: Expr, ins: Instrumentation) = TupleSelect(e, instIndex(ins))
}

class ExprInstrumenter(ictx: InstruContext) {
  val retainMatches = true

  // Should be called only if 'expr' has to be instrumented
  // Returned Expr is always an expr of type tuple (Expr, Int)
  def tupleify(e: Expr, subs: Seq[Expr], recons: Seq[Expr] => Expr)(implicit letIdMap: Map[Identifier, Identifier]): Expr = {
    // When called for:
    // Op(n1,n2,n3)
    // e      = Op(n1,n2,n3)
    // subs   = Seq(n1,n2,n3)
    // recons = { Seq(newn1,newn2,newn3) => Op(newn1, newn2, newn3) }
    //
    // This transformation should return, informally:
    //
    // LetTuple((e1,t1), transform(n1),
    //   LetTuple((e2,t2), transform(n2),
    //    ...
    //      Tuple(recons(e1, e2, ...), t1 + t2 + ... costOfExpr(Op)
    //    ...
    //   )
    // )
    //
    // You will have to handle FunctionInvocation specially here!
    tupleifyRecur(e, subs, recons, List(), Map())
  }

  def tupleifyRecur(e: Expr, subs: Seq[Expr], recons: Seq[Expr] => Expr, subeVals: List[Expr],
                    subeInsts: Map[Instrumentation, List[Expr]])(implicit letIdMap: Map[Identifier, Identifier]): Expr = {
    implicit val currFun = ictx.currFun
    import ictx._
    //note: subs.size should be zero if e is a terminal
    if (subs.size == 0) {
      e match {
        case v @ Variable(id) =>
          val valPart = if (letIdMap.contains(id)) {
            TupleSelect(letIdMap(id).toVariable, 1) //this takes care of replacement
          } else v
          val instPart = ictx.instrumenters map (_.instrument(v, Seq()))
          Tuple(valPart +: instPart)

        case t: Terminal =>
          val instPart = ictx.instrumenters map (_.instrument(t, Seq()))
          val finalRes = Tuple(t +: instPart)
          finalRes

        case _: FunctionInvocation | _: Application => tupleifyCall(e, subeVals, subeInsts)

        // TODO: We are ignoring the construction cost of fields. Fix this.
        case _ =>
          val instexprs = ictx.instrumenters.zipWithIndex.map {
            case (menter, i) => menter.instrument(e, subeInsts.getOrElse(menter.inst, List()))
          }
          Tuple(recons(subeVals) +: instexprs)
      }
    } else {
      val currExp = subs.head
      //transform the current expression
      val transCurrExpr = transform(currExp)
      val resvar = Variable(FreshIdentifier("e", transCurrExpr.getType, true))
      val eval = TupleSelect(resvar, 1)
      val instMap = insts.map { inst =>
        (inst -> (subeInsts.getOrElse(inst, List()) :+ selectInst(resvar, inst)))
      }.toMap
      //process the remaining arguments
      val recRes = tupleifyRecur(e, subs.tail, recons, subeVals :+ eval, instMap)
      Let(resvar.id, transCurrExpr, recRes)
    }
  }

  def tupleifyCall(f: Expr, subeVals: List[Expr], subeInsts: Map[Instrumentation, List[Expr]])(implicit letIdMap: Map[Identifier, Identifier]): Expr = {
    import ictx._
    implicit val currFun = ictx.currFun
    f match {
      case FunctionInvocation(TypedFunDef(fd, tps), args) =>
        if (!fd.hasLazyFieldFlag) {
          val newfd = TypedFunDef(funMap(fd), tps)
          val newFunInv = FunctionInvocation(newfd, subeVals)
          //create a variables to store the result of function invocation
          if (serialInst.instFuncs(fd)) {
            //this function is also instrumented
            val resvar = Variable(FreshIdentifier("e", newfd.returnType, true))
            val valexpr = TupleSelect(resvar, 1)
            val instexprs = ictx.instrumenters.map { m =>
              val calleeInst =
                if (serialInst.funcInsts(fd).contains(m.inst) && fd.isUserFunction) {
                  List(selectInst(resvar, m.inst))
                } else List() // ignoring fields here
              m.instrument(f, subeInsts.getOrElse(m.inst, List()) ++ calleeInst, Some(resvar)) // note: even though calleeInst is passed, it may or may not be used.
            }
            Let(resvar.id, newFunInv, Tuple(valexpr +: instexprs))
          } else {
            val resvar = Variable(FreshIdentifier("e", newFunInv.getType, true))
            val instexprs = ictx.instrumenters.map { m =>
              m.instrument(f, subeInsts.getOrElse(m.inst, List()))
            }
            Let(resvar.id, newFunInv, Tuple(resvar +: instexprs))
          }
        } else
          throw new UnsupportedOperationException("Lazy fields are not handled directly by instrumentation." +
            " Consider using the --mem option")

      case Application(fterm, args) =>
        val newApp = Application(subeVals.head, subeVals.tail)
        //create a variables to store the result of application
        if (!serialInst.instsOfLambdaType(fterm.getType.asInstanceOf[FunctionType]).isEmpty) { //the lambda is instrumented
          val resvar = Variable(FreshIdentifier("e", newApp.getType, true))
          val valexpr = TupleSelect(resvar, 1)
          val instexprs = ictx.instrumenters.map { m =>
            m.instrument(f, subeInsts.getOrElse(m.inst, List()) ++ List(selectInst(resvar, m.inst)), Some(resvar)) // note: even though calleeInst is passed, it may or may not be used.
          }
          Let(resvar.id, newApp, Tuple(valexpr +: instexprs))
        } else {
          val resvar = Variable(FreshIdentifier("e", newApp.getType, true))
          val instexprs = ictx.instrumenters.map { m =>
            m.instrument(f, subeInsts.getOrElse(m.inst, List()))
          }
          Let(resvar.id, newApp, Tuple(resvar +: instexprs))
        }
    }
  }

  /**
   * TODO: need to handle new expression trees
   * Match statements without guards are now instrumented directly
   */
  def transform(e: Expr)(implicit letIdMap: Map[Identifier, Identifier]): Expr = {
    import ictx._
    implicit val currFun = ictx.currFun
    e match {
      // Assume that none of the matchcases has a guard. It has already been converted into an if then else
      case me @ MatchExpr(scrutinee, matchCases) =>
        if (matchCases.exists(_.optGuard.isDefined)) {
          // converts match to if-then-else here.
          val condsAndRhs = for (cse <- matchCases) yield {
            val map = mapForPattern(scrutinee, cse.pattern)
            val patCond = conditionForPattern(scrutinee, cse.pattern, includeBinders = false)
            val realCond = cse.optGuard match {
              case Some(g) => And(patCond, replaceFromIDs(map, g))
              case None    => patCond
            }
            val newRhs = replaceFromIDs(map, cse.rhs)
            (realCond, newRhs)
          }
          val ite = condsAndRhs.foldRight[Expr](Error(me.getType, "Match is non-exhaustive").copiedFrom(me)) {
            case ((cond, rhs), elze) =>
              if (cond == tru) rhs else IfExpr(cond, rhs, elze)
          }
          transform(ite)
        } else {
          val transScrut = transform(scrutinee)
          val scrutRes =
            Variable(FreshIdentifier("scr", transScrut.getType, true))
          val matchExpr = MatchExpr(TupleSelect(scrutRes, 1),
            matchCases.map {
              case mCase @ MatchCase(pattern, guard, body) =>
                val transBody = transform(body)
                val bodyRes = Variable(FreshIdentifier("mc", transBody.getType, true))
                val instExprs = ictx.instrumenters map { m =>
                  m.instrumentMatchCase(me, mCase, ictx.selectInst(bodyRes, m.inst),
                    ictx.selectInst(scrutRes, m.inst))
                }
                MatchCase(pattern, guard,
                  Let(bodyRes.id, transBody, Tuple(TupleSelect(bodyRes, 1) +: instExprs)))
            })
          Let(scrutRes.id, transScrut, matchExpr)
        }

      case Let(i, v, b) =>
        val (ni, nv) = {
          val transv = transform(v)
          val ir = Variable(FreshIdentifier("ir", transv.getType, true))
          (ir, transv)
        }
        val transformedBody = transform(b)(letIdMap + (i -> ni.id))
        val r = Variable(FreshIdentifier("r", transformedBody.getType, true))
        val instexprs = instrumenters map { m =>
          m.instrument(e, List(selectInst(ni, m.inst), selectInst(r, m.inst)))
        }
        Let(ni.id, nv,
          Let(r.id, transformedBody, Tuple(TupleSelect(r, 1) +: instexprs)))

      case ife @ IfExpr(cond, th, elze) =>
        val (nifCons, condInsts) = {
          val rescond = Variable(FreshIdentifier("c", TupleType(cond.getType +: instTypes), true))
          val condInstPart = insts.map { inst => (inst -> selectInst(rescond, inst)) }.toMap
          val recons = (e1: Expr, e2: Expr) => {
            Let(rescond.id, transform(cond), IfExpr(TupleSelect(rescond, 1), e1, e2))
          }
          (recons, condInstPart)
        }
        val (nthenCons, thenInsts) = {
          val transThen = transform(th)
          val resthen = Variable(FreshIdentifier("th", transThen.getType, true))
          val thInstPart = insts.map { inst => (inst -> selectInst(resthen, inst)) }.toMap
          val recons = (theninsts: List[Expr]) => {
            Let(resthen.id, transThen, Tuple(TupleSelect(resthen, 1) +: theninsts))
          }
          (recons, thInstPart)
        }
        val (nelseCons, elseInsts) = {
          val transElze = transform(elze)
          val reselse = Variable(FreshIdentifier("el", transElze.getType, true))
          val elInstPart = insts.map { inst => (inst -> selectInst(reselse, inst)) }.toMap
          val recons = (einsts: List[Expr]) => {
            Let(reselse.id, transElze, Tuple(TupleSelect(reselse, 1) +: einsts))
          }
          (recons, elInstPart)
        }
        val (finalThInsts, finalElInsts) = instrumenters.foldLeft((List[Expr](), List[Expr]())) {
          case ((thinsts, elinsts), menter) =>
            val inst = menter.inst
            val (thinst, elinst) = menter.instrumentIfThenElseExpr(ife,
              Some(condInsts(inst)), Some(thenInsts(inst)), Some(elseInsts(inst)))
            (thinsts :+ thinst, elinsts :+ elinst)
        }
        val nthen = nthenCons(finalThInsts)
        val nelse = nelseCons(finalElInsts)
        nifCons(nthen, nelse)

      case l @ Lambda(args, body) => // instrument the lambda using a new context
        val nbody = (new ExprInstrumenter(new InstruContext(ictx.currFun,
          serialInst, serialInst.instsOfLambdaType(l.getType.asInstanceOf[FunctionType]), Some(l))))(body)
        val instexprs = instrumenters map { m => m.instrument(l, List()) } // model the time taken for constructing the lambda
        Tuple(Lambda(args, nbody) +: instexprs)

      case CaseClass(ct, args) =>
        tupleify(e, args, CaseClass(mapClassType(ct), _))

      case IsInstanceOf(arg, ct) =>
        tupleify(e, Seq(arg), (nargs: Seq[Expr]) => IsInstanceOf(nargs.head, mapClassType(ct)))

      case CaseClassSelector(ct, arg, index) =>
        tupleify(e, Seq(arg), (nargs: Seq[Expr]) => CaseClassSelector(mapClassType(ct), nargs.head, index))

      case AsInstanceOf(arg, ct) =>
        tupleify(e, Seq(arg), (nargs: Seq[Expr]) => AsInstanceOf(nargs.head, mapClassType(ct)))

      case n @ Operator(ss, recons) =>
        tupleify(e, ss, recons)

      case t: Terminal =>
        tupleify(e, Seq(), { case Seq() => t })
    }
  }

  def mapClassType[T <: ClassType](ct: T): T = {
    import ictx._
    ct match {
      case CaseClassType(cd, tps) if adtMap.contains(cd) =>
        CaseClassType(adtMap(cd).asInstanceOf[CaseClassDef], tps).asInstanceOf[T]
      case AbstractClassType(ad, tps) if adtMap.contains(ad) =>
        AbstractClassType(adtMap(ad).asInstanceOf[AbstractClassDef], tps).asInstanceOf[T]
      case _ => ct
    }
  }

  def apply(e: Expr): Expr = {
    import ictx._
    implicit val currFun = ictx.currFun
    // Apply transformations
    val newe =
      if (retainMatches) e
      else matchToIfThenElse(liftExprInMatch(e))
    val transformed = transform(newe)(Map())
    val bodyId = FreshIdentifier("bd", transformed.getType, true)
    val instExprs = instrumenters map { m =>
      m.instrumentBody(newe, selectInst(bodyId.toVariable, m.inst))
    }
    Let(bodyId, transformed,
      Tuple(TupleSelect(bodyId.toVariable, 1) +: instExprs))
  }

  def liftExprInMatch(ine: Expr): Expr = {
    def helper(e: Expr): Expr = {
      e match {
        case MatchExpr(strut, cases) => strut match {
          case t: Terminal => e
          case _ => {
            val freshid = FreshIdentifier("m", strut.getType, true)
            Let(freshid, strut, MatchExpr(freshid.toVariable, cases))
          }
        }
        case _ => e
      }
    }

    if (retainMatches) helper(ine)
    else simplePostTransform(helper)(ine)
  }
}

/**
 * Implements procedures for a specific instrumentation
 */
abstract class Instrumenter(program: Program, si: SerialInstrumenter) {

  def inst: Instrumentation

  protected val cg = CallGraphUtil.constructCallGraph(program, onlyBody = true)

  def functionsToInstrument(): Map[FunDef, List[Instrumentation]]

  def functionTypesToInstrument(): Map[FunctionType, List[Instrumentation]]

  def additionalfunctionsToAdd(): Seq[FunDef]

  def instrumentBody(bodyExpr: Expr, instExpr: Expr)(implicit fd: FunDef): Expr = instExpr

  def getRootFuncs(prog: Program = program): Set[FunDef] = {
    prog.definedFunctions.filter { fd =>
      (fd.hasPostcondition && exists(inst.isInstVariable)(fd.postcondition.get))
    }.toSet
  }

  /**
   * Given an expression to be instrumented
   * and the instrumentation of each of its subexpressions,
   * computes an instrumentation for the procedure.
   * The sub-expressions correspond to expressions returned
   * by Expression Extractors.
   * fd is the function containing the expression `e`
   */
  def instrument(e: Expr, subInsts: Seq[Expr], funInvResVar: Option[Variable] = None)(implicit fd: FunDef, letIdMap: Map[Identifier, Identifier]): Expr

  /**
   * Instrument procedure specialized for if-then-else
   */
  def instrumentIfThenElseExpr(e: IfExpr, condInst: Option[Expr],
                               thenInst: Option[Expr], elzeInst: Option[Expr]): (Expr, Expr)

  /**
   * This function is expected to combine the cost of the scrutinee,
   * the pattern matching and the expression.
   * The cost model for pattern matching is left to the user.
   * As matches with guards are converted to ifThenElse statements,
   * the user may want to make sure that the cost model for pattern
   * matching across match statements and ifThenElse statements is consistent
   */
  def instrumentMatchCase(me: MatchExpr, mc: MatchCase,
                          caseExprCost: Expr, scrutineeCost: Expr): Expr
}
/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
import Extractors._
import ExprOps._
import Types._
import Constructors._
import TypeOps.instantiateType
import xlang.Expressions._

object MethodLifting extends TransformationPhase {

  val name = "Method Lifting"
  val description = "Translate methods into functions of the companion object"

  // Takes cd and its subclasses and creates cases that together will form a composite method.
  // fdId is the method id which will be searched for in the subclasses.
  // cd is the hierarchy root
  // A Seq of MatchCases is returned, along with a boolean that signifies if the matching is complete.
  private def makeCases(cd: ClassDef, fdId: Identifier, breakDown: Expr => Expr): (Seq[MatchCase], Boolean) = cd match {
    case ccd: CaseClassDef =>

      // Common for both cases
      val ct = ccd.typed
      val binder = FreshIdentifier(ccd.id.name.toLowerCase, ct, true)
      val fBinders = (ccd.fieldsIds zip ct.fields).map(p => p._1 -> p._2.id.freshen).toMap
      def subst(e: Expr): Expr = e match {
        case CaseClassSelector(`ct`, This(`ct`), i) =>
          Variable(fBinders(i)).setPos(e)
        case This(`ct`) =>
          Variable(binder).setPos(e)
        case OldThis(`ct`) =>
          Old(binder).setPos(e)
        case e =>
          e
      }

      ccd.methods.find(_.id == fdId).map { m =>

        // Ancestor's method is a method in the case class
        val subPatts = ccd.fields map (f => WildcardPattern(Some(fBinders(f.id))))
        val patt = CaseClassPattern(Some(binder), ct, subPatts)
        val newE = simplePreTransform(subst)(breakDown(m.fullBody))
        val cse = SimpleCase(patt, newE).setPos(newE)
        (List(cse), true)

      } orElse ccd.fields.find(_.id == fdId).map { f =>

        // Ancestor's method is a case class argument in the case class
        val subPatts = ccd.fields map (fld =>
          if (fld.id == f.id)
            WildcardPattern(Some(fBinders(f.id)))
          else
            WildcardPattern(None)
        )
        val patt = CaseClassPattern(Some(binder), ct, subPatts)
        val newE = breakDown(Variable(fBinders(f.id)))
        val cse = SimpleCase(patt, newE).setPos(newE)
        (List(cse), true)

      } getOrElse {
        (List(), false)
      }

    case acd: AbstractClassDef =>
      val (r, c) = acd.knownChildren.map(makeCases(_, fdId, breakDown)).unzip
      val recs = r.flatten
      val complete = !(c contains false)
      if (complete) {
        // Children define all cases completely, we don't need to add anything
        (recs, true)
      } else if (!acd.methods.exists(m => m.id == fdId && m.body.nonEmpty)) {
        // We don't have anything to add
        (recs, false)
      } else {
        // We have something to add
        val m = acd.methods.find(m => m.id == fdId).get
        val at = acd.typed
        val binder = FreshIdentifier(acd.id.name.toLowerCase, at, true)
        val newE = simplePreTransform {
          case This(ct) => asInstOf(Variable(binder), ct)
          case e => e
        } (breakDown(m.fullBody))

        val cse = SimpleCase(InstanceOfPattern(Some(binder), at), newE).setPos(newE)
        (recs :+ cse, true)
      }
  }

  def makeInvCases(cd: ClassDef): (Seq[MatchCase], Boolean) = {
    val ct = cd.typed
    val binder = FreshIdentifier(cd.id.name.toLowerCase, ct, true)
    val fd = cd.methods.find(_.isInvariant).get

    cd match {
      case ccd: CaseClassDef =>
        val fBinders = (ccd.fieldsIds zip ct.fields).map(p => p._1 -> p._2.id.freshen).toMap

        // Ancestor's method is a method in the case class
        val subPatts = ccd.fields map (f => WildcardPattern(Some(fBinders(f.id))))
        val patt = CaseClassPattern(Some(binder), ct.asInstanceOf[CaseClassType], subPatts)
        val newE = simplePreTransform {
          case e @ CaseClassSelector(`ct`, This(`ct`), i) =>
            Variable(fBinders(i)).setPos(e)
          case e @ This(`ct`) =>
            Variable(binder).setPos(e)
          case e @ OldThis(`ct`) =>
            Old(binder).setPos(e)
          case e =>
            e
        } (fd.fullBody)

        if (newE == BooleanLiteral(true)) {
          (Nil, false)
        } else {
          val cse = SimpleCase(patt, newE).setPos(newE)
          (List(cse), true)
        }

      case acd: AbstractClassDef =>
        val (r, c) = acd.knownChildren.map(makeInvCases).unzip
        val recs = r.flatten
        val complete = !(c contains false)

        val newE = simplePreTransform {
          case This(ct) => asInstOf(Variable(binder), ct)
          case OldThis(ct) => asInstOf(Old(binder), ct)
          case e => e
        } (fd.fullBody)

        if (newE == BooleanLiteral(true)) {
          (recs, false)
        } else {
          val rhs = if (recs.isEmpty) {
            newE
          } else {
            val allCases = if (complete) recs else {
              recs :+ SimpleCase(WildcardPattern(None), BooleanLiteral(true))
            }
            and(newE, MatchExpr(binder.toVariable, allCases)).setPos(newE)
          }
          val cse = SimpleCase(InstanceOfPattern(Some(binder), ct), rhs).setPos(newE)
          (Seq(cse), true)
        }
    }
  }

  def apply(ctx: LeonContext, program: Program): Program = {

    // First we create the appropriate functions from methods:
    var mdToFds = Map[FunDef, FunDef]()
    var mdToCls = Map[FunDef, ClassDef]()

    // Lift methods to the root class
    for {
      u <- program.units
      ch <- u.classHierarchies
      c  <- ch
      if c.parent.isDefined
      fd <- c.methods
      if c.ancestors.forall(!_.methods.map{_.id}.contains(fd.id))
    } {
      val root = c.ancestors.last
      val tMap = c.typeArgs.zip(root.typeArgs).toMap
      val tSubst: TypeTree => TypeTree  = instantiateType(_, tMap)

      val fdParams = fd.params map { vd =>
        val newId = FreshIdentifier(vd.id.name, tSubst(vd.id.getType))
        vd.copy(id = newId).setPos(vd.getPos)
      }
      val paramsMap = fd.params.zip(fdParams).map{ case (from, to) => from.id -> to.id }.toMap
      val eSubst: Expr => Expr = instantiateType(_, tMap, paramsMap)

      val newFd = fd.duplicate(fd.id, fd.tparams, fdParams, tSubst(fd.returnType)) // FIXME: I don't like reusing the Identifier

      mdToCls += newFd -> c

      newFd.fullBody = eSubst(newFd.fullBody)
      newFd.decreaseMeasure = newFd.decreaseMeasure.map(eSubst)

      c.unregisterMethod(fd.id)
      root.registerMethod(newFd)
    }

    val newUnits = for (u <- program.units) yield {
      var fdsOf = Map[String, Set[FunDef]]()
      // 1) Create one function for each method
      for { cd <- u.classHierarchyRoots; fd <- cd.methods } {
        // We import class type params and freshen them
        val ctParams = cd.tparams map { _.freshen }
        val tparamsMap = cd.typeArgs.zip(ctParams map { _.tp }).toMap

        val id = fd.id.freshen
        val recType = cd.typed(ctParams.map(_.tp))
        val retType = instantiateType(fd.returnType, tparamsMap)
        val fdParams = fd.params map { vd =>
          val newId = FreshIdentifier(vd.id.name, instantiateType(vd.id.getType, tparamsMap))
          vd.copy(id = newId).setPos(vd.getPos)
        }

        val receiver = FreshIdentifier("thiss", recType).setPos(cd.id)

        val nfd = fd.duplicate(id, ctParams ++ fd.tparams, ValDef(receiver) +: fdParams, retType)
        nfd.addFlag(IsMethod(cd))

        def classPre(fd: FunDef) = mdToCls.get(fd) match {
          case None =>
            BooleanLiteral(true)
          case Some(cl) =>
            isInstOf(Variable(receiver), cl.typed(ctParams map { _.tp }))
        }

        if (cd.knownDescendants.forall(cd => (cd.methods ++ cd.fields).forall(_.id != fd.id))) {
          // Don't need to compose methods
          val paramsMap = fd.params.zip(fdParams).map { case (x,y) => (x.id, y.id) }.toMap
          def thisToReceiver(e: Expr): Option[Expr] = e match {
            case th @ This(ct) =>
              Some(asInstOf(receiver.toVariable, ct).setPos(th))
            case th @ OldThis(ct) =>
              Some(asInstOf(Old(receiver), ct).setPos(th))
            case _ =>
              None
          }

          val insTp: Expr => Expr = instantiateType(_, tparamsMap, paramsMap)
          nfd.fullBody = postMap(thisToReceiver)(insTp(nfd.fullBody))
          nfd.decreaseMeasure = nfd.decreaseMeasure.map(e => postMap(thisToReceiver)(insTp(e)))

          // Add precondition if the method was defined in a subclass
          val pre = and(classPre(fd), nfd.precOrTrue)
          nfd.fullBody = withPrecondition(nfd.fullBody, Some(pre))

        } else {
          // We need to compose methods of subclasses

          /* (Type) parameter substitutions that look at all subclasses */
          val paramsMap = (for {
            c <- cd.knownDescendants :+ cd
            m <- c.methods if m.id == fd.id
            (from,to) <- m.params zip fdParams
          } yield (from.id, to.id)).toMap

          val classParamsMap = (for {
            c <- cd.knownDescendants :+ cd
            (from, to) <- c.tparams zip ctParams
          } yield (from.tp, to.tp)).toMap

          val methodParamsMap = (for {
            c <- cd.knownDescendants :+ cd
            m <- c.methods if m.id == fd.id
            (from,to) <- m.tparams zip fd.tparams
          } yield (from.tp, to.tp)).toMap

          def inst(cs: Seq[MatchCase]) = instantiateType(
            matchExpr(Variable(receiver), cs).setPos(fd),
            classParamsMap ++ methodParamsMap,
            paramsMap + (receiver -> receiver)
          )

          if (fd.isInvariant) {
            val (cases, complete) = makeInvCases(cd)
            val allCases = if (complete) cases else {
              cases :+ SimpleCase(WildcardPattern(None), BooleanLiteral(true))
            }

            nfd.fullBody = inst(allCases).setPos(fd.getPos)
          } else {
            /* Separately handle pre, post, body */
            val (pre, _)  = makeCases(cd, fd.id, preconditionOf(_).getOrElse(BooleanLiteral(true)))
            val (post, _) = makeCases(cd, fd.id, postconditionOf(_).getOrElse(
              Lambda(Seq(ValDef(FreshIdentifier("res", retType, true))), BooleanLiteral(true))
            ))
            val (body, _) = makeCases(cd, fd.id, withoutSpec(_).getOrElse(NoTree(retType)))

            // Some simplifications
            val preSimple = {
              val nonTrivial = pre.count{ _.rhs != BooleanLiteral(true) }

              val compositePre =
                if (nonTrivial == 0) {
                  BooleanLiteral(true)
                } else {
                  inst(pre).setPos(fd.getPos)
                }

              Some(and(classPre(fd), compositePre))
            }

            val postSimple = {
              val trivial = post.forall {
                case SimpleCase(_, Lambda(_, BooleanLiteral(true))) => true
                case _ => false
              }
              if (trivial) None
              else {
                val resVal = FreshIdentifier("res", retType, true)
                Some(Lambda(
                  Seq(ValDef(resVal)),
                  inst(post map { cs => cs.copy( rhs =
                    application(cs.rhs, Seq(Variable(resVal)))
                  )})
                ).setPos(fd))
              }
            }

            val bodySimple = {
              val trivial = body forall {
                case SimpleCase(_, NoTree(_)) => true
                case _ => false
              }
              if (trivial) NoTree(retType) else inst(body)
            }

            /* Construct full body */
            nfd.fullBody = withPostcondition(
              withPrecondition(bodySimple, preSimple),
              postSimple
            )
          }
        }

        mdToFds += fd -> nfd
        fdsOf += cd.id.name -> (fdsOf.getOrElse(cd.id.name, Set()) + nfd)

        if (fd.isInvariant) cd.setInvariant(nfd)
      }

      // 2) Place functions in existing companions:
      val defs = u.defs map {
        case md: ModuleDef if fdsOf contains md.id.name =>
          val fds = fdsOf(md.id.name)
          fdsOf -= md.id.name
          ModuleDef(md.id, md.defs ++ fds, false)
        case d => d
      }

      // 3) Create missing companions
      val newCompanions = for ((name, fds) <- fdsOf) yield {
        ModuleDef(FreshIdentifier(name), fds.toSeq, false)
      }

      u.copy(defs = defs ++ newCompanions)
    }

    val pgm = Program(newUnits)

    // 4) Remove methods in classes
    for (cd <- pgm.definedClasses) {
      cd.clearMethods()
    }

    // 5) Replace method calls with function calls
    for (fd <- pgm.definedFunctions) {
      val transFun = postMap{
        case mi @ MethodInvocation(IsTyped(rec, ct: ClassType), cd, tfd, args) =>
          Some(FunctionInvocation(mdToFds(tfd.fd).typed(ct.tps ++ tfd.tps), rec +: args).setPos(mi))
        case _ => None
      } _
      fd.fullBody = transFun(fd.fullBody)
      fd.decreaseMeasure = fd.decreaseMeasure.map(transFun)
    }

    pgm
  }

}

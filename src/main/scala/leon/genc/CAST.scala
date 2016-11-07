/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import utils.{ Position, UniqueCounter }

/*
 * Here are defined classes used to represent AST of C programs.
 *
 * NOTE on char and string: because the C character and string literals
 * encoding sets are highly dependent on platforms and compilers, only
 * basic single-byte characters from the ASCII set are supported at the
 * moment.
 *
 * Details on such literals can be found in the C99 standard in §3.7,
 * §6.4.4.4 and §6.4.5, and more.
 */

object CAST { // C Abstract Syntax Tree

  /* ------------------------------------------------------------- Tree ----- */
  sealed abstract class Tree
  case object NoTree extends Tree


  /* ------------------------------------------------------------ Types ----- */
  abstract class Type(val rep: String) extends Tree {
    override def toString = rep

    def name: String = rep // usefull when the type name should be used as a variable identifier
  }
  case object NoType extends Type("???") // Used in place of a dropped type

  /* Type Modifiers */
  case class Const(typ: Type) extends Type(s"$typ const") {
    override def name: String = s"${typ.name}_const"
  }
  case class Pointer(typ: Type) extends Type(s"$typ*") {
    override def name: String = s"${typ.name}_ptr"
  }

  /* Primitive Types */
  case object Char extends Type("char")     // See NOTE on char & string
  case object Int32 extends Type("int32_t") // Requires <stdint.h>
  case object Bool extends Type("bool")     // Requires <stdbool.h>
  case object Void extends Type("void")

  /* Compound Types */
  // In order to identify structs and unions, we need to make sure they have an Id (this is used by ProgConverter).
  trait Identification { val id: Id }
  type TypeWithId = Type with Identification
  case class Struct(id: Id, fields: Seq[Var]) extends Type(id.name) with Identification
  // For union, use the factory
  class Union private (val id: Id, val fields: Seq[(Type, Id)]) extends Type(id.name) with Identification

  /* (Basic) String Type */
  // NOTE It might be better to have data+length structure
  // NOTE Currently, only string literals are supported, hence they can legally
  //      be returned from functions.
  case object String extends Type("char*") {
    override def name: String = "string"
  }

  /* Typedef */
  case class Typedef(orig: Id, alias: Id) extends Type(alias.name)

  /* Enum */
  case class Enum(id: Id, values: Seq[EnumLiteral]) extends Type(id.name)


  /* --------------------------------------------------------- Literals ----- */
  case class CharLiteral(c: Char) extends Stmt {
    require(isASCII(c)) // See NOTE on char & string
  }

  case class IntLiteral(v: Int) extends Stmt

  case class BoolLiteral(b: Boolean) extends Stmt

  case class StringLiteral(s: String) extends Stmt {
    require(isASCII(s)) // See NOTE on char & string
  }

  case class EnumLiteral(id: Id) extends Stmt


  /* ----------------------------------------------------- Definitions  ----- */
  abstract class Def extends Tree

  case class Include(file: String) extends Def {
    require(!file.isEmpty && isASCII(file))
  }

  case class Prog(
    includes:  Set[Include],
    typedefs:  Seq[Typedef],
    enums:     Seq[Enum],
    types:     Seq[Type],
    functions: Seq[Fun]
  ) extends Def

  // Manually defined function through the cCode.function annotation have a string
  // for signature+body instead of the usual Stmt AST exclusively for the body
  case class Fun(id: Id, retType: Type, params: Seq[Var], body: Either[Stmt, String]) extends Def

  case class Id(name: String) extends Def {
    // TODO add check on name's domain for conformance

    // `|` is used as the margin delimiter and can cause trouble in some situations
    def fixMargin =
      if (name.size > 0 && name(0) == '|') "| " + name
      else name
  }

  case class Var(id: Id, typ: Type) extends Def {
    require(!typ.isVoid)
  }

  /* ----------------------------------------------------------- Stmts  ----- */
  abstract class Stmt extends Tree
  case object NoStmt extends Stmt

  case class Compound(stmts: Seq[Stmt]) extends Stmt

  case class Assert(pred: Stmt, error: Option[String]) extends Stmt { // Requires <assert.h>
    require(pred.isValue)
  }

  case class DeclVar(x: Var) extends Stmt

  case class DeclInitVar(x: Var, value: Stmt) extends Stmt {
    require(value.isValue)
  }

  case class Assign(lhs: Stmt, rhs: Stmt) extends Stmt {
    require(lhs.isValue && rhs.isValue)
  }

  // Note: we don't need to differentiate between specific
  // operators so we only keep track of the "kind" of operator
  // with an Id.
  case class UnOp(op: Id, rhs: Stmt) extends Stmt {
    require(rhs.isValue)
  }

  case class MultiOp(op: Id, stmts: Seq[Stmt]) extends Stmt {
    require(stmts.length > 1 && stmts.forall { _.isValue })
  }

  case class SubscriptOp(ptr: Stmt, idx: Stmt) extends Stmt {
    require(ptr.isValue && idx.isValue)
  }

  case object Break extends Stmt

  case class Return(stmt: Stmt) extends Stmt {
    require(stmt.isValue)
  }

  case class IfElse(cond: Stmt, thn: Stmt, elze: Stmt) extends Stmt {
    require(cond.isValue)
  }

  case class While(cond: Stmt, body: Stmt) extends Stmt {
    require(cond.isValue)
  }

  case class AccessVar(id: Id) extends Stmt
  case class AccessRef(id: Id) extends Stmt
  case class AccessAddr(id: Id) extends Stmt
  case class AccessField(struct: Stmt, field: Id) extends Stmt {
    require(struct.isValue)
  }

  case class Call(id: Id, args: Seq[Stmt]) extends Stmt {
    require(args forall { _.isValue })
  }

  case class StructInit(args: Seq[(Id, Stmt)], struct: Struct) extends Stmt {
    require(args forall { _._2.isValue })
  }

  case class ArrayInit(length: Stmt, valueType: Type, defaultValue: Stmt) extends Stmt {
    require(length.isValue && defaultValue.isValue)
  }

  case class ArrayInitWithValues(valueType: Type, values: Seq[Stmt]) extends Stmt {
    require(values forall { _.isValue })

    lazy val length = values.length
  }


  /* -------------------------------------------------------- Factories ----- */
  object Literal {
    def apply(c: Char)(implicit pos: Position): CharLiteral = {
      if (isASCII(c)) CharLiteral(c)
      else unsupported("Character literals are restricted to the ASCII set")
    }

    def apply(s: String)(implicit pos: Position): StringLiteral = {
      if (isASCII(s)) StringLiteral(s)
      else unsupported("String literals are restricted to the ASCII set")
    }

    def apply(i: Int) = IntLiteral(i)
    def apply(b: Boolean) = BoolLiteral(b)
    def apply(u: Unit) = NoStmt
  }

  object Op {
    def apply(op: String, rhs: Stmt) = UnOp(Id(op), rhs)
    def apply(op: String, rhs: Stmt, lhs: Stmt) = MultiOp(Id(op), rhs :: lhs :: Nil)
    def apply(op: String, stmts: Seq[Stmt]) = MultiOp(Id(op), stmts)
  }

  object Val {
    def apply(id: Id, typ: Type) = typ match {
      case Const(_) => Var(id, typ) // avoid const of const
      case _        => Var(id, Const(typ))
    }
  }

  /* "Templatetized" Types */
  object Tuple {
    def apply(bases: Seq[Type]) = {
      val name = Id("__leon_tuple_" + bases.mkString("_") + "_t")

      val fields = bases.zipWithIndex map {
        case (typ, idx) => Var(getNthId(idx + 1), typ)
      }

      Struct(name, fields)
    }

    // Indexes start from 1, not 0!
    def getNthId(n: Int) = Id("_" + n)
  }

  object Array {
    def apply(base: Type) = {
      val name   = Id("__leon_array_" + base + "_t")
      val data   = Var(dataId, Pointer(base))
      val length = Var(lengthId, Int32)
      val fields = data :: length :: Nil

      Struct(name, fields)
    }

    def lengthId = Id("length")
    def dataId   = Id("data")
  }

  object Union {
    def apply(id: Id, types: Seq[Type]): Union = {
      val unionMembers = types map { t => (t, valueForType(t)) }
      new Union(id, unionMembers)
    }

    def unapply(u: Union): Option[(Id, Seq[(Type, Id)])] = {
      Some((u.id, u.fields))
    }

    // The "value" here refers to the identifier inside the union for inheritance.
    def valueForType(t: Type) = Id(t.name + "_value")
    def valuePathForType(t: Type) = Id("value." + t.name + "_value")
  }

  object Enum {
    // The "tag" here refers to the enumeration value used to identify a type for inheritance.
    def tagForType(t: Type) = EnumLiteral(Id("tag_" + t.name))
  }


  /* ---------------------------------------------------- Introspection ----- */
  implicit class IntrospectionOps(val stmt: Stmt) {
    def isLiteral = stmt match {
      case _: CharLiteral   => true
      case _: IntLiteral    => true
      case _: BoolLiteral   => true
      case _: StringLiteral => true
      case _: EnumLiteral   => true
      case _                => false
    }

    // True if statement can be used as a value
    def isValue: Boolean = isLiteral || {
      stmt match {
        //case _: Assign => true it's probably the case but for now let's ignore it
        case c: Compound            => c.stmts.size == 1 && c.stmts.head.isValue
        case _: UnOp                => true
        case _: MultiOp             => true
        case _: SubscriptOp         => true
        case _: AccessVar           => true
        case _: AccessRef           => true
        case _: AccessAddr          => true
        case _: AccessField         => true
        case _: Call                => true
        case _: StructInit          => true
        case _: ArrayInit           => true
        case _: ArrayInitWithValues => true
        case _                      => false
      }
    }

    def isPure: Boolean = isLiteral || {
      stmt match {
        case NoStmt                 => true
        case Compound(stmts)        => stmts forall { _.isPure }
        case Assert(pred, _)        => pred.isPure
        case UnOp(_, rhs)           => rhs.isPure
        case MultiOp(_, stmts)      => Compound(stmts).isPure
        case SubscriptOp(ptr, idx)  => (ptr ~ idx).isPure
        case IfElse(c, t, e)        => (c ~ t ~ e).isPure
        case While(c, b)            => (c ~ b).isPure
        case AccessVar(_)           => true
        case AccessRef(_)           => true
        case AccessAddr(_)          => true
        case AccessField(s, _)      => s.isPure
        // case Call(id, args)      => true if args are pure and function `id` is pure too
        case _                      => false
      }
    }

    def isPureValue = isValue && isPure
  }


  /* ------------------------------------------------------------- DSL  ----- */
  // Operator ~~ appends and flattens nested compounds
  implicit class StmtOps(val stmt: Stmt) {
    // In addition to combining statements together in a compound
    // we remove the empty ones and if the resulting compound
    // has only one statement we return this one without being
    // wrapped into a Compound
    def ~(other: Stmt) = {
      val stmts = (stmt, other) match {
        case (Compound(stmts), Compound(others)) => stmts ++ others
        case (stmt           , Compound(others)) => stmt  +: others
        case (Compound(stmts), other           ) => stmts :+ other
        case (stmt           , other           ) => stmt :: other :: Nil
      }

      def isNoStmt(s: Stmt) = s match {
        case NoStmt => true
        case _      => false
      }

      val compound = Compound(stmts filterNot isNoStmt)
      compound match {
        case Compound(stmts) if stmts.length == 0 => NoStmt
        case Compound(stmts) if stmts.length == 1 => stmts.head
        case compound                             => compound
      }
    }

    def ~~(others: Seq[Stmt]) = stmt ~ Compound(others)
  }

  implicit class StmtsOps(val stmts: Seq[Stmt]) {
    def ~~(other: Stmt) = other match {
      case Compound(others) => Compound(stmts) ~~ others
      case other            => Compound(stmts) ~ other
    }

    def ~~~(others: Seq[Stmt]) = Compound(stmts) ~~ others
  }

  val True  = BoolLiteral(true)
  val False = BoolLiteral(false)


  implicit class TypeOps(val typ: Type) {
    // Test whether a given type is made of void
    def isVoid: Boolean = typ match {
      case Void       => true
      case Const(t)   => t.isVoid
      case Pointer(t) => t.isVoid // TODO is this a good idea since it can represent anything?
      case _          => false
    }

    // Remove any const qualifier from the given type
    def removeConst: Type = typ match {
      case Const(t) => t.removeConst
      case _        => typ
    }
  }


  /* ------------------------------------------------ Fresh Generators  ----- */
  object FreshId {
    private var counter = -1
    private val leonPrefix = "__leon_"

    def apply(prefix: String = ""): Id = {
      counter += 1
      Id(leonPrefix + prefix + counter)
    }
  }

  object FreshVar {
    def apply(typ: Type, prefix: String = "") = Var(FreshId(prefix), typ)
  }

  object FreshVal {
    def apply(typ: Type, prefix: String = "") = Val(FreshId(prefix), typ)
  }

  def generateMain(_mainId: Id, return_mainResult: Boolean): Fun = {
      val id = Id("main")
      val retType = Int32
      val argc = Var(Id("argc"), Int32)
      val argv = Var(Id("argv"), Pointer(Pointer(Char)))
      val params = argc :: argv :: Nil

      val body =
        if (return_mainResult) Return(Call(_mainId, Nil))
        else Call(_mainId, Nil) ~ Return(IntLiteral(0))

      val main = Fun(id, retType, params, Left(body))

      main
  }


  /* ---------------------------------------------------------- Details ----- */
  // String & char limitations, see NOTE above
  private def isASCII(c: Char): Boolean = { c >= 0 && c <= 127 }
  private def isASCII(s: String): Boolean = s forall isASCII

  // Type of exception used to report unexpected or unsupported features
  final case class ConversionError(error: String, pos: Position) extends Exception(error)

  private[genc] def unsupported(detail: String)(implicit pos: Position) =
    throw ConversionError(s"Unsupported feature: $detail", pos)
}


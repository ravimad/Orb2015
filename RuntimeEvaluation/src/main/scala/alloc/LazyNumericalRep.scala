package allocAnalysis

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.collection._
import DigitObject._
import leon.runtimeDriver._
import scala.collection.mutable.{ListBuffer => scalaList}

object DigitObject {
  abstract class Digit
  
  case class Zero() extends Digit
  
  case class One() extends Digit
  
}

object LazyNumericalRep {
  
  abstract class NumList2
  
  
  case class Tip1() extends NumList2
  
  
  case class Spine1(head12 : DigitObject.Digit, rear21 : NumStream2) extends NumList2
  
  
  abstract class NumStream2
  
  
  case class Val1(x324 : NumList2) extends NumStream2
  
  
  case class Susp1(fun3 : () => (NumList2, BigInt)) extends NumStream2
  
  
  case class Number2(digs1 : NumStream2, schedule1 : List[NumStream2])
  
  def emptyNum = Number2(Val1(Tip1()), Nil())

  @invisibleBody
  def incalloc(xs : NumStream2): (NumList2, BigInt) = {
    val e28 = NumStream.getalloc(xs)
    val e109 = e28._2
    val bd2 = e28._1 match {
      case Tip1() =>
        (Spine1(DigitObject.One(), xs), BigInt(2) + e109)
      case s76 @ Spine1(DigitObject.Zero(), rear24) =>
        (Spine1(DigitObject.One(), rear24), BigInt(2) + e109)
      case s77 @ Spine1(_, _) =>
        val e34 = incLazyalloc(xs)
        (e34._1, e34._2 + e109)
    }
    (bd2._1, bd2._2)
  }
  
  @invisibleBody
  @invstate
  def incLazyalloc(xs : NumStream2): (NumList2, BigInt) = {
    val e36 = NumStream.getalloc(xs)
    val bd4 = {
      val Spine1(head, rear34) = e36._1
      val ir7 = DigitObject.One()
      val e38 = NumStream.getalloc(rear34)
      val e75 = e38._2
      val r163 = e38._1 match {
        case Tip1() =>
          (Spine1(DigitObject.Zero(), Val1(Spine1(ir7, rear34))), BigInt(4) + e75)
        case Spine1(DigitObject.Zero(), srearfun1) =>
          (Spine1(DigitObject.Zero(), Val1(Spine1(ir7, srearfun1))), BigInt(4) + e75)
        case s78 =>
          (Spine1(DigitObject.Zero(), Susp1(() => {
            val e51 = incLazyalloc(rear34)
            (e51._1, e51._2)
          })), BigInt(4) + e75)
      }
      (r163._1, (BigInt(1) + r163._2) + e36._2)
    }
    (bd4._1, bd4._2)
  }
  
  @invisibleBody
  def incNumalloc(w : Number2): ((NumStream2, List[NumStream2]), BigInt) = {
    val e62 = incalloc(w.digs1)
    val e102 = e62._1
    val ir6 = e102 match {
      case Spine1(DigitObject.Zero(), rear41 : Susp1) =>
        (Cons[NumStream2](rear41, w.schedule1), BigInt(1))
      case _ =>
        (w.schedule1, BigInt(0))
    }
    ((Val1(e102), ir6._1), (BigInt(1) + ir6._2) + e62._2)
  }
  
  @invisibleBody
  def Payalloc[T](q : NumStream2, scheds : List[NumStream2]): (List[NumStream2], BigInt) = {
    val bd6 = scheds match {
      case c9 @ Cons(head16, rest10) =>
        val e57 = NumStream.getalloc(head16)
        val e71 = e57._2
        val mc13 = e57._1 match {
          case Spine1(DigitObject.Zero(), rear39 : Susp1) =>
            (Cons[NumStream2](rear39, rest10), BigInt(1) + e71)
          case _ =>
            (rest10, e71)
        }
        (mc13._1, mc13._2)
      case Nil() =>
        (scheds, BigInt(0))
    }
    (bd6._1, bd6._2)
  }
  
  @invisibleBody
  def incAndPayalloc(w : Number2): (Number2, BigInt) = {
    val e15 = incNumalloc(w)
    val ir = {
      val (q, scheds) = e15._1
      ((q, scheds), e15._2)
    }
    val ir8 = ir._1
    val ir14 = ir8._1
    val e22 = Payalloc[BigInt](ir14, ir8._2)
    (Number2(ir14, e22._1), (BigInt(1) + e22._2) + ir._2)
  }

  // def main(args: Array[String]): Unit = {
  //   import scala.util.Random
  //   val rand = Random

  //   val points = (1 to 20)
  //   val size = points.map(x => ((1 << x) - 1)).toList
  //   val size2 = points.map(x => BigInt((1 << x) - 1)).to[scalaList]

  //   var ops = List[BigInt]()
  //   var orb = List[BigInt]()
  //   size.foreach { length =>
  //     var lazynum = emptyNum
  //     for (i <- 0 until length) {
  //       lazynum = incAndPayalloc(lazynum)._1
  //     }
  //     ops :+= {incAndPayalloc(lazynum)._2}
  //     orb :+= {15}
  //   }
  //   // minresults(ops, scalaList(15), List("constant"), List(), size2, "lrpincAndPay")
  //   dumpdata(size, ops, orb, "lrpincAndPay", "orb")
  // }
  /**
   * Benchmark specific parameters
   */
  abstract class RunContext {
    def coeffs: scalaList[BigInt] //from lower to higher-order terms
    def coeffNames = List("constant") // names of the coefficients
    val termsSize = 0 // number of terms (i.e monomials) in the template
    def getTermsForPoint(i: BigInt): scalaList[BigInt] = scalaList()
    def inputFromPoint(i: Int) = {
      val len = ((1 << i) - 1)
      var lazynum = emptyNum
      for (i <- 0 until len) {
        lazynum = incAndPayalloc(lazynum)._1
      }
      lazynum
    }
    val dirname = "alloc/LazyNumericalRep"
    val filePrefix: String
    val points = (3 to 18)
    val concreteInstFun: Number2 => BigInt
  }
  object MainContext extends RunContext {
    override def coeffs = scalaList[BigInt](15)
    override val filePrefix = "num" // the abbrevation used in the paper  
    override val concreteInstFun = (lazynum: Number2) => incAndPayalloc(lazynum)._2
  }
  val ctxts: scalaList[RunContext] = scalaList(MainContext)
  /**
   * Benchmark agnostic helper functions
   */
  def benchmark(ctx: RunContext) {
    import ctx._
    def template(coeffs: scalaList[BigInt], terms: scalaList[BigInt]) = {
      coeffs.head + (coeffs.tail zip terms).map { case (coeff, term) => coeff * term }.sum
    }
    def boundForInput(terms: scalaList[BigInt]): BigInt = template(coeffs, terms)
    def computeTemplate(coeffs: scalaList[BigInt], terms: scalaList[BigInt]): BigInt = {
      template(coeffs, terms)
    }
    val size = points.map(x => BigInt(x)).to[scalaList]
    val size2 = points.map(x => (x)).toList
    var ops = scalaList[BigInt]()
    var orb = scalaList[BigInt]()
    var termsforInp = (0 until termsSize).map(_ => scalaList[BigInt]()).toList
    val concreteOps = concreteInstFun
    points.foreach { i =>
      println("Processing input: " + i)
      leon.mem.clearMemo()
      val input = inputFromPoint(i)
      ops += concreteOps(input)
      // compute the static bound
      val terms = getTermsForPoint(i)
      orb += boundForInput(terms)
      terms.zipWithIndex.foreach {
        case (term, i) => termsforInp(i) += term
      }
    }
    val minlist = mindirresults(ops, coeffs, coeffNames, termsforInp, size, filePrefix, dirname)
    val minresults = minlist.map { l =>
      points.map { i =>
        computeTemplate(l, getTermsForPoint(i))
      }.to[scalaList]
    }
    dumpdirdata(size2, ops, orb, filePrefix, "dynamic", dirname)
    var i = 0
    minlist.foreach { l =>
      dumpdirdata(size2, minresults(i), orb, filePrefix, s"pareto$i", dirname)
      i = i + 1
    }
  }

  def main(args: Array[String]): Unit = {
    ctxts.foreach(benchmark)
  }
}

object NumList {
  
}

object NumStream {
  def getalloc(thiss : LazyNumericalRep.NumStream2): (LazyNumericalRep.NumList2, BigInt) = {
    val bd1 = thiss match {
      case LazyNumericalRep.Susp1(f120) =>
        val lr = lookup[LazyNumericalRep.NumList2](List(5318, thiss))
        val mc1 = if (lr._1) {
          (lr._2, BigInt(0))
        } else {
          val e26 = fvalalloc(thiss)
          (update[LazyNumericalRep.NumList2](List(5318, thiss), e26._1), BigInt(1) + e26._2)
        }
        (mc1._1, mc1._2)
      case LazyNumericalRep.Val1(x325) =>
        (x325, BigInt(0))
    }
    (bd1._1, bd1._2)
  }
  
  def fvalalloc(thiss : LazyNumericalRep.NumStream2): (LazyNumericalRep.NumList2, BigInt) = {
    val bd5 = {
      val LazyNumericalRep.Susp1(f123) = thiss
      val e55 = f123()
      (e55._1, e55._2)
    }
    (bd5._1, bd5._2)
  }
}

object Number {
  
}

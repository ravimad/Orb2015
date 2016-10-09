package stepsAnalysis

import leon.collection._
import leon._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.mem._
import leon.higherorder._
import leon.collection._
import leon.invariant._
import leon.runtimeDriver._
import scala.collection.mutable.{ ListBuffer => scalaList }

object CyclicHammingStream {

  case class SCons2(x321: BigInt, tailFun1: ValOrSusp2)

  abstract class ValOrSusp2

  case class Val1(x320: SCons2) extends ValOrSusp2

  case class Susp1(fun1: () => (SCons2, BigInt)) extends ValOrSusp2

  @invisibleBody
  def maptime(f: (BigInt) => (BigInt, BigInt), xs: SCons2): (SCons2, BigInt) = {
    val bd13 = {
      val SCons2(x, _) = xs
      val e99 = f(x)
      (SCons2(e99._1, Susp1(() => {
        val e103 = mapSusptime(f, xs)
        (e103._1, BigInt(1) + e103._2)
      })), BigInt(7) + e99._2)
    }
    (bd13._1, bd13._2)
  }

  def mapSusptime(f: (BigInt) => (BigInt, BigInt), xs: SCons2): (SCons2, BigInt) = {
    val e130 = xs.tailFun1 match {
      case s82 @ Susp1(f132) =>
        val lr3 = lookup[SCons2](List(4931, s82))
        val mc10 = if (lr3._1) {
          (lr3._2, BigInt(1))
        } else {
          val e129 = ValOrSusp.fvaltime(s82)
          (update[SCons2](List(4931, s82), e129._1), BigInt(3) + e129._2)
        }
        (mc10._1, BigInt(4) + mc10._2)
      case Val1(x326) =>
        (x326, BigInt(5))
    }
    val e131 = maptime(f, e130._1)
    (e131._1, (BigInt(1) + e131._2) + e130._2)
  }

  def mintime(x: BigInt, y: BigInt, z: BigInt): (BigInt, BigInt) = {
    val bd15 = if (x <= y) {
      val th7 = if (x <= z) {
        (x, BigInt(2))
      } else {
        (z, BigInt(2))
      }
      (th7._1, BigInt(2) + th7._2)
    } else {
      val el8 = if (y <= z) {
        (y, BigInt(2))
      } else {
        (z, BigInt(2))
      }
      (el8._1, BigInt(2) + el8._2)
    }
    (bd15._1, bd15._2)
  }

  @invisibleBody
  def mergetime(a: SCons2, b: SCons2, c: SCons2): (SCons2, BigInt) = {
    val e94 = mintime(a.x321, b.x321, c.x321)
    (SCons2(e94._1, Susp1(() => {
      val e86 = mergeSusptime(a, b, c)
      (e86._1, BigInt(1) + e86._2)
    })), BigInt(7) + e94._2)
  }

  @invisibleBody
  def forcetime(a: SCons2): (SCons2, BigInt) = {
    val bd5 = a.tailFun1 match {
      case s79 @ Susp1(f129) =>
        val lr = lookup[SCons2](List(4931, s79))
        val mc2 = if (lr._1) {
          (lr._2, BigInt(1))
        } else {
          val e38 = ValOrSusp.fvaltime(s79)
          (update[SCons2](List(4931, s79), e38._1), BigInt(3) + e38._2)
        }
        (mc2._1, BigInt(4) + mc2._2)
      case Val1(x323) =>
        (x323, BigInt(5))
    }
    (bd5._1, bd5._2)
  }

  @invisibleBody
  def mergeSusptime(a: SCons2, b: SCons2, c: SCons2): (SCons2, BigInt) = {
    val e45 = mintime(a.x321, b.x321, c.x321)
    val e163 = e45._1
    val c28 = BigInt(2)
    val ir2 = if (a.x321 == e163) {
      val e47 = forcetime(a)
      (e47._1, (BigInt(2) + c28) + e47._2)
    } else {
      (a, BigInt(1) + c28)
    }
    val c30 = BigInt(2)
    val ir3 = if (b.x321 == e163) {
      val e52 = forcetime(b)
      (e52._1, (BigInt(2) + c30) + e52._2)
    } else {
      (b, BigInt(1) + c30)
    }
    val c32 = BigInt(2)
    val ir4 = if (c.x321 == e163) {
      val e57 = forcetime(c)
      (e57._1, (BigInt(2) + c32) + e57._2)
    } else {
      (c, BigInt(1) + c32)
    }
    val e64 = mergetime(ir2._1, ir3._1, ir4._1)
    (e64._1, ((((BigInt(5) + e64._2) + ir4._2) + ir3._2) + ir2._2) + e45._2)
  }

  @invisibleBody
  def nexttime(f: SCons2, s: SCons2): (SCons2, BigInt) = {
    val bd16 = s.tailFun1 match {
      case s81 @ Susp1(f131) =>
        val lr2 = lookup[SCons2](List(4931, s81))
        val mc8 = if (lr2._1) {
          (lr2._2, BigInt(1))
        } else {
          val e125 = ValOrSusp.fvaltime(s81)
          (update[SCons2](List(4931, s81), e125._1), BigInt(3) + e125._2)
        }
        (mc8._1, BigInt(4) + mc8._2)
      case Val1(x325) =>
        (x325, BigInt(5))
    }
    (bd16._1, bd16._2)
  }

  @invisibleBody
  def nthElemAfterSecondtime(n: BigInt, f: SCons2, s: SCons2): (BigInt, BigInt) = {
    val e108 = nexttime(f, s)
    val bd14 = {
      val t370 @ SCons2(x, _) = e108._1
      val mc7 = if (n == BigInt(2)) {
        (x, BigInt(2))
      } else {
        val e114 = nthElemAfterSecondtime(n - BigInt(1), s, t370)
        (e114._1, BigInt(4) + e114._2)
      }
      (mc7._1, (BigInt(4) + mc7._2) + e108._2)
    }
    (bd14._1, bd14._2)
  }

  val hamstreamtime: (SCons2, BigInt) = (SCons2(BigInt(1), Susp1(() => {
    val e66 = hamGentime
    (e66._1, BigInt(1) + e66._2)
  })), BigInt(3))

  @invisibleBody
  def hamGentime(): (SCons2, BigInt) = {
    val e138 = hamstreamtime._1
    val e21 = maptime((x$6: BigInt) => (BigInt(2) * x$6, BigInt(1)), e138)
    val e27 = maptime((x$7: BigInt) => (BigInt(3) * x$7, BigInt(1)), e138)
    val e33 = maptime((x$8: BigInt) => (BigInt(5) * x$8, BigInt(1)), e138)
    val e35 = mergetime(e21._1, e27._1, e33._1)
    (e35._1, (((BigInt(8) + e35._2) + e33._2) + e27._2) + e21._2)
  }

  def nthHammingNumbertime(n: BigInt): (BigInt, BigInt) = {
    val e194 = hamstreamtime._1
    val r164 = if (n == BigInt(0)) {
      (e194.x321, BigInt(3))
    } else {
      val ir6 = e194.tailFun1 match {
        case s80 @ Susp1(f130) =>
          val lr1 = lookup[SCons2](List(4931, s80))
          val mc4 = if (lr1._1) {
            (lr1._2, BigInt(1))
          } else {
            val e73 = ValOrSusp.fvaltime(s80)
            (update[SCons2](List(4931, s80), e73._1), BigInt(3) + e73._2)
          }
          (mc4._1, BigInt(4) + mc4._2)
        case Val1(x324) =>
          (x324, BigInt(5))
      }
      val r163 = if (n == BigInt(1)) {
        (ir6._1.x321, BigInt(3))
      } else {
        val e78 = nthElemAfterSecondtime(n, e194, ir6._1)
        (e78._1, BigInt(3) + e78._2)
      }
      (r163._1, (BigInt(2) + r163._2) + ir6._2)
    }
    (r164._1, BigInt(1) + r164._2)
  }

  //  def main(args: Array[String]): Unit = {
  //    import scala.util.Random
  //    val rand = Random
  //
  //    val points = (0 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
  //    val size = points.map(x => BigInt(x)).to[scalaList]
  //    
  //    var ops = scalaList[BigInt]()
  //    points.foreach { i =>
  //      val input = i
  //      ops :+= {
  //          leon.mem.clearMemo()
  //          nthHammingNumbertime(input)._2
  //      }
  //    }
  //    minresults(ops, scalaList(4, 129), List("constant", "n"), List(size), size, "hamcyc")
  //  } 

  /**
   * Benchmark specific parameters
   */
  def coeffs = scalaList[BigInt](4, 129) //from lower to higher-order terms
  def coeffNames = List("constant", "n") // names of the coefficients
  val termsSize = 1 // number of terms (i.e monomials) in the template
  def getTermsForPoint(i: BigInt) = scalaList(i)
  def inputFromPoint(i: Int) = i
  val dirname = "CyclicHammingStream"
  val filePrefix = "hams" // the abbrevation used in the paper
  val points = (0 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
  val concreteInstFun = (input: BigInt) => nthHammingNumbertime(input)._2

  /**
   * Benchmark agnostic helper functions
   */
  def template(coeffs: scalaList[BigInt], terms: scalaList[BigInt]) = {
    coeffs.head + (coeffs.tail zip terms).map { case (coeff, term) => coeff * term }.sum
  }
  def boundForInput(terms: scalaList[BigInt]): BigInt = template(coeffs, terms)
  def computeTemplate(coeffs: scalaList[BigInt], terms: scalaList[BigInt]): BigInt = {
    template(coeffs, terms)
  }

  def main(args: Array[String]): Unit = {
    val size = points.map(x => BigInt(x)).to[scalaList]
    val size2 = points.map(x => (x)).toList
    var ops = scalaList[BigInt]()
    var orb = scalaList[BigInt]()
    var termsforInp = (0 until termsSize).map(_ => scalaList[BigInt]()).toList
    val concreteOps = concreteInstFun
    points.foreach { i =>
      println("Processing input: " + i)
      val input = inputFromPoint(i)
      ops += concreteOps(input)
      // compute the static bound
      val terms = getTermsForPoint(i)
      orb += boundForInput(terms)
      terms.zipWithIndex.foreach {
        case (term, i) => termsforInp(i) += term
      }
      leon.mem.clearMemo()
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
      dumpdirdata(size2, ops, minresults(i), filePrefix, s"pareto$i", dirname)
      i = i + 1
    }
  }
  object ValOrSusp {
    def fvaltime(thiss: CyclicHammingStream.ValOrSusp2): (CyclicHammingStream.SCons2, BigInt) = {
      val bd = thiss match {
        case CyclicHammingStream.Susp1(f128) =>
          val e15 = f128()
          (e15._1, BigInt(4) + e15._2)
        case CyclicHammingStream.Val1(x322) =>
          (x322, BigInt(4))
      }
      (bd._1, bd._2)
    }
  }
}



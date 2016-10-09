package stepsAnalysis

import leon.collection._
import leon._
import leon.mem._
import leon.higherorder._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.collection._
import leon.runtimeDriver._
import scala.collection.mutable.{ ListBuffer => scalaList }

object LazySelectionSort {

  abstract class LList2

  case class SCons1(x316: BigInt, tailFun1: Stream2) extends LList2

  case class SNil1() extends LList2

  case class Stream2(lfun1: () => (LList2, BigInt))

  def pullMintime(l: List[BigInt]): (List[BigInt], BigInt) = {
    val bd4 = l match {
      case Nil() =>
        (l, BigInt(2))
      case Cons(x, xs) =>
        val e34 = pullMintime(xs)
        val scr6 = BigInt(1) + e34._2
        val mc7 = e34._1 match {
          case Nil() =>
            (List[BigInt](x), BigInt(4) + scr6)
          case nxs @ Cons(y, ys) =>
            val mc6 = if (x <= y) {
              (Cons[BigInt](x, nxs), BigInt(3))
            } else {
              (Cons[BigInt](y, Cons[BigInt](x, ys)), BigInt(4))
            }
            (mc6._1, (BigInt(5) + mc6._2) + scr6)
        }
        (mc7._1, BigInt(5) + mc7._2)
    }
    (bd4._1, bd4._2)
  }

  def sorttime(l: List[BigInt]): (LList2, BigInt) = {
    val e15 = pullMintime(l)
    val scr8 = BigInt(1) + e15._2
    val bd1 = e15._1 match {
      case Cons(x, xs) =>
        (SCons1(x, Stream2(() => {
          val e18 = sorttime(xs)
          (e18._1, BigInt(1) + e18._2)
        })), BigInt(7) + scr8)
      case _ =>
        (SNil1(), BigInt(3) + scr8)
    }
    (bd1._1, bd1._2)
  }

  def concattime(l1: List[BigInt], l2: LList2): (LList2, BigInt) = {
    val bd6 = l1 match {
      case Cons(x, xs) =>
        (SCons1(x, Stream2(() => {
          val e48 = concattime(xs, l2)
          (e48._1, BigInt(1) + e48._2)
        })), BigInt(7))
      case Nil() =>
        (SNil1(), BigInt(4))
    }
    (bd6._1, bd6._2)
  }

  def kthMintime(l: Stream2, k: BigInt): (BigInt, BigInt) = {
    val lr = lookup[LList2](List(4888, l))
    val scr1 = if (lr._1) {
      (lr._2, BigInt(1))
    } else {
      val e25 = Stream.listtime(l)
      (update[LList2](List(4888, l), e25._1), BigInt(3) + e25._2)
    }
    val bd3 = scr1._1 match {
      case SCons1(x, xs36) =>
        val mc2 = if (k == BigInt(1)) {
          (x, BigInt(2))
        } else {
          val e30 = kthMintime(xs36, k - BigInt(1))
          (e30._1, BigInt(4) + e30._2)
        }
        (mc2._1, (BigInt(4) + mc2._2) + scr1._2)
      case SNil1() =>
        (BigInt(0), BigInt(3) + scr1._2)
    }
    (bd3._1, bd3._2)
  }

  /**
   * Benchmark specific parameters
   */
  def coeffs = scalaList[BigInt](37, 15) //from lower to higher-order terms
  def coeffNames = List("constant", "3*length") // names of the coefficients
  val termsSize = 1 // number of terms (i.e monomials) in the template
  def getTermsForPoint(length: BigInt) = scalaList(3 * length)
  def inputFromPoint(length: Int) = {
    val tinput = {
      (1 to length).foldLeft[List[BigInt]](Nil()) { (f, n) =>
        Cons(n, f)
      }
    }
    val input = sorttime(tinput)._1 match {
      case SCons1(_, t) => t
      case SNil1()      => Stream2(() => (SNil1(), 0))
    }
    input
  }
  val dirname = "LazySelectionSort"
  val filePrefix = "sel" // the abbrevation used in the paper
  val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
  val concreteInstFun = (input: Stream2) => kthMintime(input, 3)._2

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
      dumpdirdata(size2, minresults(i), orb, filePrefix, s"pareto$i", dirname)
      i = i + 1
    }
  }

  object Stream {
    def listtime(thiss: LazySelectionSort.Stream2): (LazySelectionSort.LList2, BigInt) = {
      val e23 = thiss.lfun1()
      (e23._1, BigInt(2) + e23._2)
    }
  }

}
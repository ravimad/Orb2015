package allocAnalysis

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
import scala.collection.mutable.{ListBuffer => scalaList}

object CyclicFibStream {
  
  case class SCons2(x320 : BigInt, tailFun1 : ValOrSusp2)
  
  
  abstract class ValOrSusp2
  
  
  case class Val1(x319 : SCons2) extends ValOrSusp2
  
  
  case class Susp1(fun1 : () => (SCons2, BigInt)) extends ValOrSusp2
  
  def zipWithFunalloc(f : (BigInt, BigInt) => (BigInt, BigInt), xs : SCons2, ys : SCons2): (SCons2, BigInt) = {
    val bd6 = {
      val (SCons2(x, _), SCons2(y, _)) = (xs, ys)
      val e63 = f(x, y)
      (SCons2(e63._1, Susp1(() => {
        val e68 = zipWithSuspalloc(f, xs, ys)
        (e68._1, e68._2)
      })), BigInt(3) + e63._2)
    }
    (bd6._1, bd6._2)
  }
  
  def zipWithSuspalloc(f : (BigInt, BigInt) => (BigInt, BigInt), xs : SCons2, ys : SCons2): (SCons2, BigInt) = {
    val e21 = xs.tailFun1 match {
      case s80 @ Susp1(f128) =>
        val lr1 = lookup[SCons2](List(4903, s80))
        val mc2 = if (lr1._1) {
          (lr1._2, BigInt(0))
        } else {
          val e20 = ValOrSusp.fvalalloc(s80)
          (update[SCons2](List(4903, s80), e20._1), BigInt(1) + e20._2)
        }
        (mc2._1, mc2._2)
      case Val1(x322) =>
        (x322, BigInt(0))
    }
    val e25 = ys.tailFun1 match {
      case s81 @ Susp1(f129) =>
        val lr2 = lookup[SCons2](List(4903, s81))
        val mc4 = if (lr2._1) {
          (lr2._2, BigInt(0))
        } else {
          val e24 = ValOrSusp.fvalalloc(s81)
          (update[SCons2](List(4903, s81), e24._1), BigInt(1) + e24._2)
        }
        (mc4._1, mc4._2)
      case Val1(x323) =>
        (x323, BigInt(0))
    }
    val e26 = zipWithFunalloc(f, e21._1, e25._1)
    (e26._1, (e26._2 + e25._2) + e21._2)
  }
  
  @invisibleBody
  def nextalloc(f : SCons2, s : SCons2, t : SCons2): (SCons2, BigInt) = {
    val bd = t.tailFun1 match {
      case s79 @ Susp1(f127) =>
        val lr = lookup[SCons2](List(4903, s79))
        val mc = if (lr._1) {
          (lr._2, BigInt(0))
        } else {
          val e16 = ValOrSusp.fvalalloc(s79)
          (update[SCons2](List(4903, s79), e16._1), BigInt(1) + e16._2)
        }
        (mc._1, mc._2)
      case Val1(x321) =>
        (x321, BigInt(0))
    }
    (bd._1, bd._2)
  }
  
  @invisibleBody
  def nthElemAfterThirdalloc(n : BigInt, f : SCons2, s : SCons2, t : SCons2): (BigInt, BigInt) = {
    val e83 = nextalloc(f, s, t)
    val bd10 = {
      val fourth1 @ SCons2(x, _) = e83._1
      val mc15 = if (n == BigInt(3)) {
        (x, BigInt(0))
      } else {
        val e90 = nthElemAfterThirdalloc(n - BigInt(1), s, t, fourth1)
        (e90._1, e90._2)
      }
      (mc15._1, mc15._2 + e83._2)
    }
    (bd10._1, bd10._2)
  }
  
  val fibstreamalloc : (SCons2, BigInt) = (SCons2(BigInt(0), Val1(SCons2(BigInt(1), Susp1(() => {
    val e73 = genNextalloc
    (e73._1, e73._2)
  })))), BigInt(5))
  
  @invisibleBody
  def genNextalloc(): (SCons2, BigInt) = {
    val e131 = fibstreamalloc._1
    val e35 = e131.tailFun1 match {
      case s82 @ Susp1(f130) =>
        val lr3 = lookup[SCons2](List(4903, s82))
        val mc6 = if (lr3._1) {
          (lr3._2, BigInt(0))
        } else {
          val e34 = ValOrSusp.fvalalloc(s82)
          (update[SCons2](List(4903, s82), e34._1), BigInt(1) + e34._2)
        }
        (mc6._1, mc6._2)
      case Val1(x324) =>
        (x324, BigInt(0))
    }
    val e36 = zipWithFunalloc((x$3 : BigInt, x$4 : BigInt) => (x$3 + x$4, BigInt(0)), e131, e35._1)
    (e36._1, (BigInt(1) + e36._2) + e35._2)
  }
  
  def nthFiballoc(n : BigInt): (BigInt, BigInt) = {
    val e114 = fibstreamalloc._1
    val r161 = if (n == BigInt(0)) {
      (e114.x320, BigInt(0))
    } else {
      val ir2 = e114.tailFun1 match {
        case s83 @ Susp1(f131) =>
          val lr4 = lookup[SCons2](List(4903, s83))
          val mc8 = if (lr4._1) {
            (lr4._2, BigInt(0))
          } else {
            val e41 = ValOrSusp.fvalalloc(s83)
            (update[SCons2](List(4903, s83), e41._1), BigInt(1) + e41._2)
          }
          (mc8._1, mc8._2)
        case Val1(x325) =>
          (x325, BigInt(0))
      }
      val r160 = if (n == BigInt(1)) {
        (ir2._1.x320, BigInt(0))
      } else {
        val e43 = (ir2._1, BigInt(0))
        val ir3 = ir2._1.tailFun1 match {
          case s84 @ Susp1(f132) =>
            val lr5 = lookup[SCons2](List(4903, s84))
            val mc10 = if (lr5._1) {
              (lr5._2, BigInt(0))
            } else {
              val e45 = ValOrSusp.fvalalloc(s84)
              (update[SCons2](List(4903, s84), e45._1), BigInt(1) + e45._2)
            }
            (mc10._1, mc10._2 + e43._2)
          case Val1(x326) =>
            (x326, e43._2)
        }
        val r159 = if (n == BigInt(2)) {
          (ir3._1.x320, BigInt(0))
        } else {
          val e51 = nthElemAfterThirdalloc(n, e114, ir2._1, ir3._1)
          (e51._1, e51._2)
        }
        (r159._1, r159._2 + ir3._2)
      }
      (r160._1, r160._2 + ir2._2)
    }
    (r161._1, r161._2)
  }

  // def main(args: Array[String]): Unit = {
  //   import scala.util.Random
  //   val rand = Random

  //   val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 20000 by 1000)
  //   val size = points.map(x => (x)).toList

  //   var ops = List[BigInt]()
  //   var orb = List[BigInt]()
  //   points.foreach { i =>
  //     val input = i
  //     ops :+= {
  //         leon.mem.clearMemo()
  //         nthFiballoc(input)._2
  //     }
  //     orb :+= {4*i}
  //   }
  //   // minresults(ops, scalaList(0, 4), List("constant", "n"), List(size), size, "fibcycalloc")
  //   dumpdata(size, ops, orb, "fibcyc", "orb")
  // }  
  /**
   * Benchmark specific parameters
   */
  def coeffs = scalaList[BigInt](0, 4) //from lower to higher-order terms
  def coeffNames = List("constant", "n") // names of the coefficients
  val termsSize = 1 // number of terms (i.e monomials) in the template
  def getTermsForPoint(i: BigInt) = scalaList(i)
  def inputFromPoint(i: Int) = i 
  val dirname = "alloc/CyclicFibonacciStream"
  val filePrefix = "fibs" // the abbrevation used in the paper
  val points = (0 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
  val concreteInstFun = (input: BigInt) => nthFiballoc(input)._2

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
      //inputfori += //{BigInt(i*i)}
      // We should not clear the cache to measure this
      // orb2 :+= {15*i - 18}     
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
  
}

object SCons {
  
}

object ValOrSusp {
  def fvalalloc(thiss : CyclicFibStream.ValOrSusp2): (CyclicFibStream.SCons2, BigInt) = {
    val bd9 = thiss match {
      case CyclicFibStream.Susp1(f133) =>
        val e79 = f133()
        (e79._1, e79._2)
      case CyclicFibStream.Val1(x327) =>
        (x327, BigInt(0))
    }
    (bd9._1, bd9._2)
  }
}

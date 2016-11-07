package stepsAnalysis

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.runtimeDriver._
import scala.collection.mutable.{ListBuffer => scalaList}

object HammingMemoized {
  abstract class IList

  case class Cons(x : BigInt, tail : IList) extends IList

  case class Nil() extends IList

  case class Data(v : BigInt, i2 : BigInt, i3 : BigInt, i5 : BigInt)

  /*@invstate
  @memoize
  def hamtime(n : BigInt): (Data, BigInt) = {
    val bd1 = if (n == BigInt(0)) {
      (Data(BigInt(1), BigInt(0), BigInt(0), BigInt(0)), BigInt(3))
    } else {
      val e164 = n - BigInt(1)
      val lr1 = lookup[Data](List(4877, e164))
      val scr = if (lr1._1) {
        (lr1._2, BigInt(2))
      } else {
        val e24 = hamtime(e164)
        (update[Data](List(4877, e164), e24._1), BigInt(4) + e24._2)
      }
      val ir = {
        val Data(x, i2, i3, i5) = scr._1
        ((x, i2, i3, i5), BigInt(7) + scr._2)
      }
      val ir2 = (ir._1._2, BigInt(1))
      val e31 = (ir._1, BigInt(0))
      val ir3 = (ir._1._3, BigInt(1) + e31._2)
      val ir4 = (ir._1._4, BigInt(1))
      val e33 = (ir2._1, BigInt(0))
      val lr2 = lookup[Data](List(4877, ir2._1))
      val e35 = if (lr2._1) {
        (lr2._2, BigInt(1) + e33._2)
      } else {
        val e34 = hamtime(ir2._1)
        (update[Data](List(4877, ir2._1), e34._1), (BigInt(3) + e34._2) + e33._2)
      }
      val e36 = (e35._1.v, BigInt(1) + e35._2)
      val ir5 = (e35._1.v * BigInt(2), BigInt(1) + e36._2)
      val e38 = (ir3._1, BigInt(0))
      val lr3 = lookup[Data](List(4877, ir3._1))
      val e40 = if (lr3._1) {
        (lr3._2, BigInt(1) + e38._2)
      } else {
        val e39 = hamtime(ir3._1)
        (update[Data](List(4877, ir3._1), e39._1), (BigInt(3) + e39._2) + e38._2)
      }
      val ir6 = (e40._1.v * BigInt(3), BigInt(2) + e40._2)
      val e43 = (ir4._1, BigInt(0))
      val lr4 = lookup[Data](List(4877, ir4._1))
      val e45 = if (lr4._1) {
        (lr4._2, BigInt(1) + e43._2)
      } else {
        val e44 = hamtime(ir4._1)
        (update[Data](List(4877, ir4._1), e44._1), (BigInt(3) + e44._2) + e43._2)
      }
      val e46 = (e45._1.v, BigInt(1) + e45._2)
      val ir7 = (e45._1.v * BigInt(5), BigInt(1) + e46._2)
      val e130 = (ir5._1, BigInt(0))
      val e131 = (ir6._1, BigInt(0))
      val e132 = (ir5._1 == ir6._1, (BigInt(1) + e131._2) + e130._2)
      val e133 = (ir6._1, BigInt(0))
      val e134 = (ir7._1, BigInt(0))
      val e135 = (ir6._1 == ir7._1, (BigInt(1) + e134._2) + e133._2)
      val c11 = (e132._1 && e135._1, (((BigInt(3) + e134._2) + e133._2) + e131._2) + e130._2)
      val scr1 = if (e132._1 && e135._1) {
        ((ir5._1, BigInt(1) + ir2._1, BigInt(1) + ir3._1, BigInt(1) + ir4._1), BigInt(5) + c11._2)
      } else {
        val e124 = (ir5._1, BigInt(0))
        val e125 = (ir6._1, BigInt(0))
        val e126 = (ir5._1 == ir6._1, (BigInt(1) + e125._2) + e124._2)
        val e127 = (ir5._1, BigInt(0))
        val e128 = (ir7._1, BigInt(0))
        val e129 = (ir5._1 < ir7._1, (BigInt(1) + e128._2) + e127._2)
        val c12 = (e126._1 && e129._1, (((BigInt(3) + e128._2) + e127._2) + e125._2) + e124._2)
        val el5 = if (e126._1 && e129._1) {
          ((ir5._1, BigInt(1) + ir2._1, BigInt(1) + ir3._1, ir4._1), BigInt(4) + c12._2)
        } else {
          val e118 = (ir5._1, BigInt(0))
          val e119 = (ir7._1, BigInt(0))
          val e120 = (ir5._1 == ir7._1, (BigInt(1) + e119._2) + e118._2)
          val e121 = (ir5._1, BigInt(0))
          val e122 = (ir6._1, BigInt(0))
          val e123 = (ir5._1 < ir6._1, (BigInt(1) + e122._2) + e121._2)
          val c13 = (e120._1 && e123._1, (((BigInt(3) + e122._2) + e121._2) + e119._2) + e118._2)
          val el4 = if (e120._1 && e123._1) {
            ((ir5._1, BigInt(1) + ir2._1, ir3._1, BigInt(1) + ir4._1), BigInt(4) + c13._2)
          } else {
            val e112 = (ir6._1, BigInt(0))
            val e113 = (ir7._1, BigInt(0))
            val e114 = (ir6._1 == ir7._1, (BigInt(1) + e113._2) + e112._2)
            val e115 = (ir6._1, BigInt(0))
            val e116 = (ir5._1, BigInt(0))
            val e117 = (ir6._1 < ir5._1, (BigInt(1) + e116._2) + e115._2)
            val c14 = (e114._1 && e117._1, (((BigInt(3) + e116._2) + e115._2) + e113._2) + e112._2)
            val el3 = if (e114._1 && e117._1) {
              ((ir6._1, ir2._1, BigInt(1) + ir3._1, BigInt(1) + ir4._1), BigInt(4) + c14._2)
            } else {
              val e106 = (ir5._1, BigInt(0))
              val e107 = (ir6._1, BigInt(0))
              val e108 = (ir5._1 < ir6._1, (BigInt(1) + e107._2) + e106._2)
              val e109 = (ir5._1, BigInt(0))
              val e110 = (ir7._1, BigInt(0))
              val e111 = (ir5._1 < ir7._1, (BigInt(1) + e110._2) + e109._2)
              val c15 = (e108._1 && e111._1, (((BigInt(3) + e110._2) + e109._2) + e107._2) + e106._2)
              val el2 = if (e108._1 && e111._1) {
                ((ir5._1, BigInt(1) + ir2._1, ir3._1, ir4._1), BigInt(3) + c15._2)
              } else {
                val e100 = (ir6._1, BigInt(0))
                val e101 = (ir7._1, BigInt(0))
                val e102 = (ir6._1 < ir7._1, (BigInt(1) + e101._2) + e100._2)
                val e103 = (ir6._1, BigInt(0))
                val e104 = (ir5._1, BigInt(0))
                val e105 = (ir6._1 < ir5._1, (BigInt(1) + e104._2) + e103._2)
                val c16 = (e102._1 && e105._1, (((BigInt(3) + e104._2) + e103._2) + e101._2) + e100._2)
                val el1 = if (e102._1 && e105._1) {
                  ((ir6._1, ir2._1, BigInt(1) + ir3._1, ir4._1), BigInt(3) + c16._2)
                } else {
                  ((ir7._1, ir2._1, ir3._1, BigInt(1) + ir4._1), BigInt(3) + c16._2)
                }
                (el1._1, (BigInt(1) + c15._2) + el1._2)
              }
              (el2._1, (BigInt(1) + c14._2) + el2._2)
            }
            (el3._1, (BigInt(1) + c13._2) + el3._2)
          }
          (el4._1, (BigInt(1) + c12._2) + el4._2)
        }
        (el5._1, (BigInt(1) + c11._2) + el5._2)
      }
      val ir8 = {
        val (v, ni, nj, nk) = scr1._1
        ((v, ni, nj, nk), BigInt(7) + scr1._2)
      }
      (Data(ir8._1._1, ir8._1._2, ir8._1._3, ir8._1._4), (((((BigInt(15) + ir8._2) + e46._2) + e40._2) + e36._2) + e31._2) + ir._2)
    }
    (bd1._1, bd1._2)
  }*/

  def hamtime(n : BigInt): (Data, BigInt) = {
    val bd1 = if (n == BigInt(0)) {
      (Data(BigInt(1), BigInt(0), BigInt(0), BigInt(0)), BigInt(3))
    } else {
      val e186 = n - BigInt(1)
      val lr0 =  lookup[Data](List(4877, e186))
      val scr0 = if (lr0._1) {
        (lr0._2, BigInt(2))
      } else {
        val e52 = hamtime(e186)
        ( update[Data](List(4877, e186), e52._1), BigInt(4) + e52._2)
      }
      val ir1 = {
        val Data(x, i2, i3, i5) = scr0._1
        ((x, i2, i3, i5), BigInt(7) + scr0._2)
      }
      val ir3 = (ir1._1._2, BigInt(1))
      val e59 = (ir1._1, BigInt(0))
      val ir4 = (ir1._1._3, BigInt(1) + e59._2)
      val ir5 = (ir1._1._4, BigInt(1))
      val e61 = (ir3._1, BigInt(0))
      val lr1 =  lookup[Data](List(4877, ir3._1))
      val e63 = if (lr1._1) {
        (lr1._2, BigInt(1) + e61._2)
      } else {
        val e62 = hamtime(ir3._1)
        ( update[Data](List(4877, ir3._1), e62._1), (BigInt(3) + e62._2) + e61._2)
      }
      val e64 = (e63._1.v, BigInt(1) + e63._2)
      val ir6 = (e63._1.v * BigInt(2), BigInt(1) + e64._2)
      val e66 = (ir4._1, BigInt(0))
      val lr2 =  lookup[Data](List(4877, ir4._1))
      val e68 = if (lr2._1) {
        (lr2._2, BigInt(1) + e66._2)
      } else {
        val e67 = hamtime(ir4._1)
        ( update[Data](List(4877, ir4._1), e67._1), (BigInt(3) + e67._2) + e66._2)
      }
      val ir7 = (e68._1.v * BigInt(3), BigInt(2) + e68._2)
      val e71 = (ir5._1, BigInt(0))
      val lr3 =  lookup[Data](List(4877, ir5._1))
      val e73 = if (lr3._1) {
        (lr3._2, BigInt(1) + e71._2)
      } else {
        val e72 = hamtime(ir5._1)
        ( update[Data](List(4877, ir5._1), e72._1), (BigInt(3) + e72._2) + e71._2)
      }
      val e74 = (e73._1.v, BigInt(1) + e73._2)
      val ir8 = (e73._1.v * BigInt(5), BigInt(1) + e74._2)
      val e158 = (ir6._1, BigInt(0))
      val e159 = (ir7._1, BigInt(0))
      val e160 = (ir6._1 == ir7._1, (BigInt(1) + e159._2) + e158._2)
      val e161 = (ir7._1, BigInt(0))
      val e162 = (ir8._1, BigInt(0))
      val e163 = (ir7._1 == ir8._1, (BigInt(1) + e162._2) + e161._2)
      val c17 = (e160._1 && e163._1, (((BigInt(3) + e162._2) + e161._2) + e159._2) + e158._2)
      val scr1 = if (e160._1 && e163._1) {
        ((ir6._1, BigInt(1) + ir3._1, BigInt(1) + ir4._1, BigInt(1) + ir5._1), BigInt(5) + c17._2)
      } else {
        val e152 = (ir6._1, BigInt(0))
        val e153 = (ir7._1, BigInt(0))
        val e154 = (ir6._1 == ir7._1, (BigInt(1) + e153._2) + e152._2)
        val e155 = (ir6._1, BigInt(0))
        val e156 = (ir8._1, BigInt(0))
        val e157 = (ir6._1 < ir8._1, (BigInt(1) + e156._2) + e155._2)
        val c18 = (e154._1 && e157._1, (((BigInt(3) + e156._2) + e155._2) + e153._2) + e152._2)
        val el6 = if (e154._1 && e157._1) {
          ((ir6._1, BigInt(1) + ir3._1, BigInt(1) + ir4._1, ir5._1), BigInt(4) + c18._2)
        } else {
          val e146 = (ir6._1, BigInt(0))
          val e147 = (ir8._1, BigInt(0))
          val e148 = (ir6._1 == ir8._1, (BigInt(1) + e147._2) + e146._2)
          val e149 = (ir6._1, BigInt(0))
          val e150 = (ir7._1, BigInt(0))
          val e151 = (ir6._1 < ir7._1, (BigInt(1) + e150._2) + e149._2)
          val c19 = (e148._1 && e151._1, (((BigInt(3) + e150._2) + e149._2) + e147._2) + e146._2)
          val el5 = if (e148._1 && e151._1) {
            ((ir6._1, BigInt(1) + ir3._1, ir4._1, BigInt(1) + ir5._1), BigInt(4) + c19._2)
          } else {
            val e140 = (ir7._1, BigInt(0))
            val e141 = (ir8._1, BigInt(0))
            val e142 = (ir7._1 == ir8._1, (BigInt(1) + e141._2) + e140._2)
            val e143 = (ir7._1, BigInt(0))
            val e144 = (ir6._1, BigInt(0))
            val e145 = (ir7._1 < ir6._1, (BigInt(1) + e144._2) + e143._2)
            val c20 = (e142._1 && e145._1, (((BigInt(3) + e144._2) + e143._2) + e141._2) + e140._2)
            val el4 = if (e142._1 && e145._1) {
              ((ir7._1, ir3._1, BigInt(1) + ir4._1, BigInt(1) + ir5._1), BigInt(4) + c20._2)
            } else {
              val e134 = (ir6._1, BigInt(0))
              val e135 = (ir7._1, BigInt(0))
              val e136 = (ir6._1 < ir7._1, (BigInt(1) + e135._2) + e134._2)
              val e137 = (ir6._1, BigInt(0))
              val e138 = (ir8._1, BigInt(0))
              val e139 = (ir6._1 < ir8._1, (BigInt(1) + e138._2) + e137._2)
              val c21 = (e136._1 && e139._1, (((BigInt(3) + e138._2) + e137._2) + e135._2) + e134._2)
              val el3 = if (e136._1 && e139._1) {
                ((ir6._1, BigInt(1) + ir3._1, ir4._1, ir5._1), BigInt(3) + c21._2)
              } else {
                val e128 = (ir7._1, BigInt(0))
                val e129 = (ir8._1, BigInt(0))
                val e130 = (ir7._1 < ir8._1, (BigInt(1) + e129._2) + e128._2)
                val e131 = (ir7._1, BigInt(0))
                val e132 = (ir6._1, BigInt(0))
                val e133 = (ir7._1 < ir6._1, (BigInt(1) + e132._2) + e131._2)
                val c22 = (e130._1 && e133._1, (((BigInt(3) + e132._2) + e131._2) + e129._2) + e128._2)
                val el2 = if (e130._1 && e133._1) {
                  ((ir7._1, ir3._1, BigInt(1) + ir4._1, ir5._1), BigInt(3) + c22._2)
                } else {
                  ((ir8._1, ir3._1, ir4._1, BigInt(1) + ir5._1), BigInt(3) + c22._2)
                }
                (el2._1, (BigInt(1) + c21._2) + el2._2)
              }
              (el3._1, (BigInt(1) + c20._2) + el3._2)
            }
            (el4._1, (BigInt(1) + c19._2) + el4._2)
          }
          (el5._1, (BigInt(1) + c18._2) + el5._2)
        }
        (el6._1, (BigInt(1) + c17._2) + el6._2)
      }
      val r159 = {
        val (v, ni, nj, nk) = scr1._1
        (Data(v, ni, nj, nk), BigInt(7) + scr1._2)
      }
      (r159._1, (((((BigInt(10) + r159._2) + e74._2) + e68._2) + e64._2) + e59._2) + ir1._2)
    }
    (bd1._1, bd1._2)
  }

  def invoketime(n : BigInt): (BigInt, BigInt) = {
    val lr = lookup[Data](List(4877, n))
    val e16 = if (lr._1) {
      (lr._2, BigInt(1))
    } else {
      val e15 = hamtime(n)
      (update[Data](List(4877, n), e15._1), BigInt(3) + e15._2)
    }
    (e16._1.v, BigInt(1) + e16._2)
  }

  def hammingListtime(n : BigInt): (IList, BigInt) = {
    val bd2 = if (n == BigInt(0)) {
      val e151 = invoketime(n)
      (Cons(e151._1, Nil()), BigInt(5) + e151._2)
    } else {
      val e157 = hammingListtime(n - BigInt(1))
      val e159 = invoketime(n)
      (Cons(e159._1, e157._1), (BigInt(6) + e159._2) + e157._2)
    }
    (bd2._1, bd2._2)
  }

//  def main(args: Array[String]): Unit = {
//    import scala.util.Random
//    val rand = Random
//
//    val points = (0 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
//    val size = points.map(x => BigInt(x)).to[scalaList]
//    val size2 = points.map(x => (x)).toList
//
//    var ops = List[BigInt]()
//    var orb = List[BigInt]()
//    points.foreach { i =>
//      val input = i
//      ops :+= {62*i + 70
//          // leon.mem.clearMemo()
//          // hammingListtime(input)._2
//      }
//      orb :+= {71*i + 70}
//    }
//    dumpdata(size2, ops, orb, "hammem", "orb")
//    minresults(ops, scalaList(70, 71), List("constant", "n"), List(size), size, "hammem")
//  }
      /**
   * Benchmark specific parameters
   */
  def coeffs = scalaList[BigInt](65, 66) //from lower to higher-order terms
  def coeffNames = List("constant", "n") // names of the coefficients
  val termsSize = 1 // number of terms (i.e monomials) in the template
  def getTermsForPoint(i: BigInt) = {
    scalaList(i)
  }
  def inputFromPoint(i: Int) = {
    i
  }
  val dirname = "steps/HammingMemoized"
  val filePrefix = "hm"
  val points =  (0 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
  val concreteInstFun = (input: BigInt) => hammingListtime(input)._2

  /**
   * Benchmark agnostic helper functions
   */
  def template(coeffs: scalaList[BigInt], terms: scalaList[BigInt]) = {
    coeffs.head + (coeffs.tail zip terms).map{ case (coeff, term) => coeff * term }.sum
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
    var termsforInp = (0 until termsSize).map( _ =>scalaList[BigInt]()).toList
    val concreteOps = concreteInstFun
    points.foreach { i =>
      println("Processing input: "+i)
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

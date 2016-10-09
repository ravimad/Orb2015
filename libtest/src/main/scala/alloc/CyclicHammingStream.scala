package CyclicHammingStreamalloc

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

object MergeAndHammingNumbers {
  
  case class SCons2(x321 : BigInt, tailFun1 : ValOrSusp2)
  
  
  abstract class ValOrSusp2
  
  
  case class Val1(x320 : SCons2) extends ValOrSusp2
  
  
  case class Susp1(fun1 : () => (SCons2, BigInt)) extends ValOrSusp2
  
  @invisibleBody
  def mapalloc(f : (BigInt) => (BigInt, BigInt), xs : SCons2): (SCons2, BigInt) = {
    val bd13 = {
      val SCons2(x, _) = xs
      val e99 = f(x)
      (SCons2(e99._1, Susp1(() => {
        val e103 = mapSuspalloc(f, xs)
        (e103._1, e103._2)
      })), BigInt(3) + e99._2)
    }
    (bd13._1, bd13._2)
  }
  
  def mapSuspalloc(f : (BigInt) => (BigInt, BigInt), xs : SCons2): (SCons2, BigInt) = {
    val e130 = xs.tailFun1 match {
      case s82 @ Susp1(f132) =>
        val lr3 = lookup[SCons2](List(4934, s82))
        val mc10 = if (lr3._1) {
          (lr3._2, BigInt(0))
        } else {
          val e129 = ValOrSusp.fvalalloc(s82)
          (update[SCons2](List(4934, s82), e129._1), BigInt(1) + e129._2)
        }
        (mc10._1, mc10._2)
      case Val1(x326) =>
        (x326, BigInt(0))
    }
    val e131 = mapalloc(f, e130._1)
    (e131._1, e131._2 + e130._2)
  }
  
  def minalloc(x : BigInt, y : BigInt, z : BigInt): (BigInt, BigInt) = {
    val bd15 = if (x <= y) {
      val th7 = if (x <= z) {
        (x, BigInt(0))
      } else {
        (z, BigInt(0))
      }
      (th7._1, th7._2)
    } else {
      val el8 = if (y <= z) {
        (y, BigInt(0))
      } else {
        (z, BigInt(0))
      }
      (el8._1, el8._2)
    }
    (bd15._1, bd15._2)
  }
  
  @invisibleBody
  def mergealloc(a : SCons2, b : SCons2, c : SCons2): (SCons2, BigInt) = {
    val e92 = minalloc(a.x321, b.x321, c.x321)
    (SCons2(e92._1, Susp1(() => {
      val e84 = mergeSuspalloc(a, b, c)
      (e84._1, e84._2)
    })), BigInt(3) + e92._2)
  }
  
  @invisibleBody
  def forcealloc(a : SCons2): (SCons2, BigInt) = {
    val bd4 = a.tailFun1 match {
      case s79 @ Susp1(f128) =>
        val lr = lookup[SCons2](List(4934, s79))
        val mc = if (lr._1) {
          (lr._2, BigInt(0))
        } else {
          val e36 = ValOrSusp.fvalalloc(s79)
          (update[SCons2](List(4934, s79), e36._1), BigInt(1) + e36._2)
        }
        (mc._1, mc._2)
      case Val1(x322) =>
        (x322, BigInt(0))
    }
    (bd4._1, bd4._2)
  }
  
  @invisibleBody
  def mergeSuspalloc(a : SCons2, b : SCons2, c : SCons2): (SCons2, BigInt) = {
    val e43 = minalloc(a.x321, b.x321, c.x321)
    val e202 = e43._1
    val ir2 = if (a.x321 == e202) {
      val e45 = forcealloc(a)
      (e45._1, e45._2)
    } else {
      (a, BigInt(0))
    }
    val ir3 = if (b.x321 == e202) {
      val e50 = forcealloc(b)
      (e50._1, e50._2)
    } else {
      (b, BigInt(0))
    }
    val ir4 = if (c.x321 == e202) {
      val e55 = forcealloc(c)
      (e55._1, e55._2)
    } else {
      (c, BigInt(0))
    }
    val e62 = mergealloc(ir2._1, ir3._1, ir4._1)
    (e62._1, (((e62._2 + ir4._2) + ir3._2) + ir2._2) + e43._2)
  }
  
  @invisibleBody
  def nextalloc(f : SCons2, s : SCons2): (SCons2, BigInt) = {
    val bd16 = s.tailFun1 match {
      case s81 @ Susp1(f131) =>
        val lr2 = lookup[SCons2](List(4934, s81))
        val mc8 = if (lr2._1) {
          (lr2._2, BigInt(0))
        } else {
          val e125 = ValOrSusp.fvalalloc(s81)
          (update[SCons2](List(4934, s81), e125._1), BigInt(1) + e125._2)
        }
        (mc8._1, mc8._2)
      case Val1(x325) =>
        (x325, BigInt(0))
    }
    (bd16._1, bd16._2)
  }
  
  @invisibleBody
  def nthElemAfterSecondalloc(n : BigInt, f : SCons2, s : SCons2): (BigInt, BigInt) = {
    val e108 = nextalloc(f, s)
    val bd14 = {
      val t370 @ SCons2(x, _) = e108._1
      val mc7 = if (n == BigInt(2)) {
        (x, BigInt(0))
      } else {
        val e114 = nthElemAfterSecondalloc(n - BigInt(1), s, t370)
        (e114._1, e114._2)
      }
      (mc7._1, mc7._2 + e108._2)
    }
    (bd14._1, bd14._2)
  }
  
  val hamstreamalloc : (SCons2, BigInt) = (SCons2(BigInt(1), Susp1(() => {
    val e64 = hamGenalloc
    (e64._1, e64._2)
  })), BigInt(3))
  
  @invisibleBody
  def hamGenalloc(): (SCons2, BigInt) = {
    val e141 = hamstreamalloc._1
    val e19 = mapalloc((x$6 : BigInt) => (BigInt(2) * x$6, BigInt(0)), e141)
    val e25 = mapalloc((x$7 : BigInt) => (BigInt(3) * x$7, BigInt(0)), e141)
    val e31 = mapalloc((x$8 : BigInt) => (BigInt(5) * x$8, BigInt(0)), e141)
    val e33 = mergealloc(e19._1, e25._1, e31._1)
    (e33._1, (((BigInt(3) + e33._2) + e31._2) + e25._2) + e19._2)
  }
  
  def nthHammingNumberalloc(n : BigInt): (BigInt, BigInt) = {
    val e177 = hamstreamalloc._1
    val r164 = if (n == BigInt(0)) {
      (e177.x321, BigInt(0))
    } else {
      val ir6 = e177.tailFun1 match {
        case s80 @ Susp1(f129) =>
          val lr1 = lookup[SCons2](List(4934, s80))
          val mc2 = if (lr1._1) {
            (lr1._2, BigInt(0))
          } else {
            val e71 = ValOrSusp.fvalalloc(s80)
            (update[SCons2](List(4934, s80), e71._1), BigInt(1) + e71._2)
          }
          (mc2._1, mc2._2)
        case Val1(x323) =>
          (x323, BigInt(0))
      }
      val r163 = if (n == BigInt(1)) {
        (ir6._1.x321, BigInt(0))
      } else {
        val e76 = nthElemAfterSecondalloc(n, e177, ir6._1)
        (e76._1, e76._2)
      }
      (r163._1, r163._2 + ir6._2)
    }
    (r164._1, r164._2)
  }
  
  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    val size = points.map(x => (x)).toList
    
    var ops = List[BigInt]()
    var orb = List[BigInt]()
    points.foreach { i =>
      val input = i
      ops :+= {
          leon.mem.clearMemo()
          nthHammingNumberalloc(input)._2
      }
      orb :+= {16*i}
    }
    // minresults(ops, scalaList(0, 16), List("constant", "n"), List(size), size, "hamcyc")
    dumpdata(size, ops, orb, "hamcyc", "orb")
  } 

}

object SCons {
  
}

object ValOrSusp {
  def fvalalloc(thiss : MergeAndHammingNumbers.ValOrSusp2): (MergeAndHammingNumbers.SCons2, BigInt) = {
    val bd11 = thiss match {
      case MergeAndHammingNumbers.Susp1(f130) =>
        val e96 = f130()
        (e96._1, e96._2)
      case MergeAndHammingNumbers.Val1(x324) =>
        (x324, BigInt(0))
    }
    (bd11._1, bd11._2)
  }
}

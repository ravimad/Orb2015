package CyclicFibStream

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

object ZipWithAndFibStream {
  
  case class SCons2(x320 : BigInt, tailFun1 : ValOrSusp2)
  
  
  abstract class ValOrSusp2
  
  
  case class Val1(x319 : SCons2) extends ValOrSusp2
  
  
  case class Susp1(fun1 : () => (SCons2, BigInt)) extends ValOrSusp2
  
  def zipWithFuntime(f : (BigInt, BigInt) => (BigInt, BigInt), xs : SCons2, ys : SCons2): (SCons2, BigInt) = {
    val bd7 = {
      val (SCons2(x, _), SCons2(y, _)) = (xs, ys)
      val e65 = f(x, y)
      (SCons2(e65._1, Susp1(() => {
        val e70 = zipWithSusptime(f, xs, ys)
        (e70._1, BigInt(1) + e70._2)
      })), BigInt(13) + e65._2)
    }
    (bd7._1, bd7._2)
  }
  
  def zipWithSusptime(f : (BigInt, BigInt) => (BigInt, BigInt), xs : SCons2, ys : SCons2): (SCons2, BigInt) = {
    val e21 = xs.tailFun1 match {
      case s80 @ Susp1(f128) =>
        val lr1 = lookup[SCons2](List(4900, s80))
        val mc2 = if (lr1._1) {
          (lr1._2, BigInt(1))
        } else {
          val e20 = ValOrSusp.fvaltime(s80)
          (update[SCons2](List(4900, s80), e20._1), BigInt(3) + e20._2)
        }
        (mc2._1, BigInt(4) + mc2._2)
      case Val1(x322) =>
        (x322, BigInt(5))
    }
    val e25 = ys.tailFun1 match {
      case s81 @ Susp1(f129) =>
        val lr2 = lookup[SCons2](List(4900, s81))
        val mc4 = if (lr2._1) {
          (lr2._2, BigInt(1))
        } else {
          val e24 = ValOrSusp.fvaltime(s81)
          (update[SCons2](List(4900, s81), e24._1), BigInt(3) + e24._2)
        }
        (mc4._1, BigInt(4) + mc4._2)
      case Val1(x323) =>
        (x323, BigInt(5))
    }
    val e26 = zipWithFuntime(f, e21._1, e25._1)
    (e26._1, ((BigInt(1) + e26._2) + e25._2) + e21._2)
  }
  
  @invisibleBody
  def nexttime(f : SCons2, s : SCons2, t : SCons2): (SCons2, BigInt) = {
    val bd = t.tailFun1 match {
      case s79 @ Susp1(f127) =>
        val lr = lookup[SCons2](List(4900, s79))
        val mc = if (lr._1) {
          (lr._2, BigInt(1))
        } else {
          val e16 = ValOrSusp.fvaltime(s79)
          (update[SCons2](List(4900, s79), e16._1), BigInt(3) + e16._2)
        }
        (mc._1, BigInt(4) + mc._2)
      case Val1(x321) =>
        (x321, BigInt(5))
    }
    (bd._1, bd._2)
  }
  
  @invisibleBody
  def nthElemAfterThirdtime(n : BigInt, f : SCons2, s : SCons2, t : SCons2): (BigInt, BigInt) = {
    val e83 = nexttime(f, s, t)
    val bd10 = {
      val fourth1 @ SCons2(x, _) = e83._1
      val mc15 = if (n == BigInt(3)) {
        (x, BigInt(2))
      } else {
        val e90 = nthElemAfterThirdtime(n - BigInt(1), s, t, fourth1)
        (e90._1, BigInt(4) + e90._2)
      }
      (mc15._1, (BigInt(4) + mc15._2) + e83._2)
    }
    (bd10._1, bd10._2)
  }
  
  val fibstreamtime : (SCons2, BigInt) = (SCons2(BigInt(0), Val1(SCons2(BigInt(1), Susp1(() => {
    val e75 = genNexttime
    (e75._1, BigInt(1) + e75._2)
  })))), BigInt(5))
  
  @invisibleBody
  def genNexttime(): (SCons2, BigInt) = {
    val e121 = fibstreamtime._1
    val e37 = e121.tailFun1 match {
      case s82 @ Susp1(f131) =>
        val lr3 = lookup[SCons2](List(4900, s82))
        val mc8 = if (lr3._1) {
          (lr3._2, BigInt(1))
        } else {
          val e36 = ValOrSusp.fvaltime(s82)
          (update[SCons2](List(4900, s82), e36._1), BigInt(3) + e36._2)
        }
        (mc8._1, BigInt(4) + mc8._2)
      case Val1(x325) =>
        (x325, BigInt(5))
    }
    val e38 = zipWithFuntime((x$3 : BigInt, x$4 : BigInt) => (x$3 + x$4, BigInt(1)), e121, e37._1)
    (e38._1, (BigInt(3) + e38._2) + e37._2)
  }
  
  def nthFibtime(n : BigInt): (BigInt, BigInt) = {
    val e111 = fibstreamtime._1
    val r161 = if (n == BigInt(0)) {
      (e111.x320, BigInt(3))
    } else {
      val ir2 = e111.tailFun1 match {
        case s83 @ Susp1(f132) =>
          val lr4 = lookup[SCons2](List(4900, s83))
          val mc10 = if (lr4._1) {
            (lr4._2, BigInt(1))
          } else {
            val e43 = ValOrSusp.fvaltime(s83)
            (update[SCons2](List(4900, s83), e43._1), BigInt(3) + e43._2)
          }
          (mc10._1, BigInt(4) + mc10._2)
        case Val1(x326) =>
          (x326, BigInt(5))
      }
      val r160 = if (n == BigInt(1)) {
        (ir2._1.x320, BigInt(3))
      } else {
        val scr6 = (ir2._1.tailFun1, BigInt(1))
        val ir3 = ir2._1.tailFun1 match {
          case s84 @ Susp1(f133) =>
            val lr5 = lookup[SCons2](List(4900, s84))
            val mc12 = if (lr5._1) {
              (lr5._2, BigInt(1))
            } else {
              val e47 = ValOrSusp.fvaltime(s84)
              (update[SCons2](List(4900, s84), e47._1), BigInt(3) + e47._2)
            }
            (mc12._1, (BigInt(3) + mc12._2) + scr6._2)
          case Val1(x327) =>
            (x327, BigInt(4) + scr6._2)
        }
        val r159 = if (n == BigInt(2)) {
          (ir3._1.x320, BigInt(3))
        } else {
          val e53 = nthElemAfterThirdtime(n, e111, ir2._1, ir3._1)
          (e53._1, BigInt(3) + e53._2)
        }
        (r159._1, (BigInt(2) + r159._2) + ir3._2)
      }
      (r160._1, (BigInt(2) + r160._2) + ir2._2)
    }
    (r161._1, BigInt(1) + r161._2)
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (0 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    val size = points.map(x => BigInt(x)).to[scalaList]
    
    var ops = scalaList[BigInt]()
    points.foreach { i =>
      val input = i
      ops :+= {
          leon.mem.clearMemo()
          nthFibtime(input)._2
      }
    }

    minresults(ops, scalaList(4, 45), List("constant", "n"), List(size), size, "fibcyc")
  }  
  
}

object SCons {
  
}

object ValOrSusp {
  def fvaltime(thiss : ZipWithAndFibStream.ValOrSusp2): (ZipWithAndFibStream.SCons2, BigInt) = {
    val bd2 = thiss match {
      case ZipWithAndFibStream.Susp1(f130) =>
        val e28 = f130()
        (e28._1, BigInt(4) + e28._2)
      case ZipWithAndFibStream.Val1(x324) =>
        (x324, BigInt(4))
    }
    (bd2._1, bd2._2)
  }
}

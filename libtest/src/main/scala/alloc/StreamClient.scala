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
import StreamLibrary._

object StreamClient {
  def mapClientalloc(n : BigInt): (BigInt, BigInt) = {
    val e147 = StreamLibrary.natsFromnalloc(BigInt(0))
    val e149 = StreamLibrary.mapalloc((n : BigInt) => {
      val e144 = StreamLibrary.constFun1alloc(n)
      (e144._1, e144._2)
    }, e147._1)
    val e151 = nthElemAfterMapalloc(n, e149._1)
    (e151._1, (e151._2 + e149._2) + e147._2)
  }
  
  def nthElemAfterMapalloc(n : BigInt, s : StreamLibrary.LList2): (BigInt, BigInt) = {
    val bd11 = s match {
      case StreamLibrary.SNil1() =>
        (BigInt(0), BigInt(0))
      case s108 @ StreamLibrary.SCons1(x, _) =>
        val mc11 = if (n == BigInt(0)) {
          (x, BigInt(0))
        } else {
          val e79 = LList.tailOrNilalloc(s108)
          val e81 = nthElemAfterMapalloc(n - BigInt(1), e79._1)
          (e81._1, e81._2 + e79._2)
        }
        (mc11._1, mc11._2)
    }
    (bd11._1, bd11._2)
  }
  
  def nthElemInRepeatalloc(n : BigInt, s : StreamLibrary.LList2): (BigInt, BigInt) = {
    val bd19 = s match {
      case StreamLibrary.SNil1() =>
        (BigInt(0), BigInt(0))
      case s111 @ StreamLibrary.SCons1(x, _) =>
        val mc25 = if (n == BigInt(0)) {
          (x, BigInt(0))
        } else {
          val e124 = LList.tailOrNilalloc(s111)
          val e126 = nthElemInRepeatalloc(n - BigInt(1), e124._1)
          (e126._1, e126._2 + e124._2)
        }
        (mc25._1, mc25._2)
    }
    (bd19._1, bd19._2)
  }
  
  def takeWhileClientalloc(n : BigInt): (BigInt, BigInt) = {
    val e34 = StreamLibrary.natsFromnalloc(BigInt(0))
    val e36 = StreamLibrary.takeWhilealloc((n : BigInt) => {
      val e31 = StreamLibrary.constFun2alloc(n)
      (e31._1, e31._2)
    }, e34._1)
    val e38 = nthElemAfterTakeWhilealloc(n, e36._1)
    (e38._1, (e38._2 + e36._2) + e34._2)
  }
  
  def nthElemAfterTakeWhilealloc(n : BigInt, s : StreamLibrary.LList2): (BigInt, BigInt) = {
    val bd17 = s match {
      case StreamLibrary.SNil1() =>
        (BigInt(0), BigInt(0))
      case s109 @ StreamLibrary.SCons1(x, _) =>
        val mc21 = if (n == BigInt(0)) {
          (x, BigInt(0))
        } else {
          val e106 = LList.tailOrNilalloc(s109)
          val e108 = nthElemAfterTakeWhilealloc(n - BigInt(1), e106._1)
          (e108._1, e108._2 + e106._2)
        }
        (mc21._1, mc21._2)
    }
    (bd17._1, bd17._2)
  }
  
  def scanClientalloc(n : BigInt): (BigInt, BigInt) = {
    val e204 = StreamLibrary.natsFromnalloc(BigInt(0))
    val e206 = StreamLibrary.scanalloc((n : BigInt, m : BigInt) => {
      val e200 = StreamLibrary.constFun3alloc(n, m)
      (e200._1, e200._2)
    }, BigInt(0), e204._1)
    val e208 = nthElemAfterScanalloc(n, e206._1)
    (e208._1, (e208._2 + e206._2) + e204._2)
  }
  
  def nthElemAfterScanalloc(n : BigInt, s : StreamLibrary.LList2): (BigInt, BigInt) = {
    val bd18 = s match {
      case StreamLibrary.SNil1() =>
        (BigInt(0), BigInt(0))
      case s110 @ StreamLibrary.SCons1(x, _) =>
        val mc23 = if (n == BigInt(0)) {
          (x, BigInt(0))
        } else {
          val e115 = LList.tailOrNilalloc(s110)
          val e117 = nthElemAfterScanalloc(n - BigInt(1), e115._1)
          (e117._1, e117._2 + e115._2)
        }
        (mc23._1, mc23._2)
    }
    (bd18._1, bd18._2)
  }
  
  def unfoldClientalloc(n : BigInt, c : BigInt): (BigInt, BigInt) = {
    val e26 = StreamLibrary.unfoldalloc((n : BigInt) => {
      val e23 = StreamLibrary.constFun4alloc(n)
      (e23._1, e23._2)
    }, c)
    val e28 = nthElemAfterUnfoldalloc(n, e26._1)
    (e28._1, e28._2 + e26._2)
  }
  
  def nthElemAfterUnfoldalloc(n : BigInt, s : StreamLibrary.LList2): (BigInt, BigInt) = {
    val bd8 = s match {
      case StreamLibrary.SNil1() =>
        (BigInt(0), BigInt(0))
      case s106 @ StreamLibrary.SCons1(x, _) =>
        val mc7 = if (n == BigInt(0)) {
          (x, BigInt(0))
        } else {
          val e53 = LList.tailOrNilalloc(s106)
          val e55 = nthElemAfterUnfoldalloc(n - BigInt(1), e53._1)
          (e55._1, e55._2 + e53._2)
        }
        (mc7._1, mc7._2)
    }
    (bd8._1, bd8._2)
  }
  
  def zipWithClientalloc(n : BigInt): (BigInt, BigInt) = {
    val e184 = StreamLibrary.natsFromnalloc(BigInt(0))
    val e187 = StreamLibrary.natsFromnalloc(BigInt(0))
    val e189 = StreamLibrary.zipWithalloc((n : BigInt, m : BigInt) => {
      val e181 = StreamLibrary.constFun3alloc(n, m)
      (e181._1, e181._2)
    }, e184._1, e187._1)
    val e191 = nthElemAfterZipWithalloc(n, e189._1)
    (e191._1, ((e191._2 + e189._2) + e187._2) + e184._2)
  }
  
  def nthElemAfterZipWithalloc(n : BigInt, s : StreamLibrary.LList2): (BigInt, BigInt) = {
    val bd9 = s match {
      case StreamLibrary.SNil1() =>
        (BigInt(0), BigInt(0))
      case s107 @ StreamLibrary.SCons1(x, _) =>
        val mc9 = if (n == BigInt(0)) {
          (x, BigInt(0))
        } else {
          val e62 = LList.tailOrNilalloc(s107)
          val e64 = nthElemAfterZipWithalloc(n - BigInt(1), e62._1)
          (e64._1, e64._2 + e62._2)
        }
        (mc9._1, mc9._2)
    }
    (bd9._1, bd9._2)
  }
  
}

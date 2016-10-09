package PrimeStreamalloc

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
import scala.collection.mutable.{ListBuffer => scalaList}

object RunningExample {
  abstract class Bool
  
  case class True() extends Bool
  
  case class False() extends Bool
  
  
  abstract class Stream2
  
  
  case class SCons1(x318 : (BigInt, Bool), tailFun1 : () => (Stream2, BigInt)) extends Stream2
  
  
  case class SNil1() extends Stream2
  
  val primeStreamalloc : (SCons1, BigInt) = (SCons1((BigInt(1), True()), () => {
    val e62 = nextElemalloc(BigInt(2))
    (e62._1, e62._2)
  }), BigInt(3))
  
  def isPrimeRecalloc(i : BigInt, n : BigInt): (Bool, BigInt) = {
    val bd = if (i == BigInt(1)) {
      (True(), BigInt(1))
    } else {
      val el1 = if ({
        assert(i != BigInt(0), "Division by zero")
        n / i
      } * i == n) {
        (False(), BigInt(1))
      } else {
        val e18 = isPrimeRecalloc(i - BigInt(1), n)
        (e18._1, e18._2)
      }
      (el1._1, el1._2)
    }
    (bd._1, bd._2)
  }
  
  def isPrimeNumalloc(n : BigInt): (Bool, BigInt) = {
    val e57 = isPrimeRecalloc(n - BigInt(1), n)
    (e57._1, e57._2)
  }
  
  def nextElemalloc(i : BigInt): (Stream2, BigInt) = {
    val e38 = isPrimeNumalloc(i)
    val ir5 = BigInt(1) + i
    (SCons1((i, e38._1), () => {
      val e44 = nextElemalloc(ir5)
      (e44._1, e44._2)
    }), BigInt(2) + e38._2)
  }
  
  def isPrimeSalloc(s : Stream2, i : BigInt): (Boolean, BigInt) = {
    val bd2 = s match {
      case SNil1() =>
        (true, BigInt(0))
      case SCons1(x, tfun1) =>
        val e34 = nextElemalloc(i)
        val temp1 = () => {
          val e34 = nextElemalloc(i)
          (e34._1, e34._2)
        }
        (tfun1 == temp1, BigInt(1))
    }
    (bd2._1, bd2._2)
  }
  
  def primesUntilNalloc(n : BigInt): (List[BigInt], BigInt) = {
    val e52 = takeRecalloc(BigInt(0), n - BigInt(2), primeStreamalloc._1)
    (e52._1, e52._2)
  }
  
  def takeRecalloc(i : BigInt, n : BigInt, s : Stream2): (List[BigInt], BigInt) = {
    val bd9 = s match {
      case c13 @ SCons1((x, b), _) =>
        val mc2 = if (i < n) {
          val lr = lookup[Stream2](List(4889, c13))
          val e70 = if (lr._1) {
            (lr._2, BigInt(0))
          } else {
            val e69 = Stream.tailalloc(c13)
            (update[Stream2](List(4889, c13), e69._1), BigInt(1) + e69._2)
          }
          val e71 = takeRecalloc(BigInt(1) + i, n, e70._1)
          val r167 = if (b == True()) {
            (Cons[BigInt](x, e71._1), BigInt(2))
          } else {
            (e71._1, BigInt(1))
          }
          (r167._1, (r167._2 + e71._2) + e70._2)
        } else {
          (List[BigInt](), BigInt(1))
        }
        (mc2._1, mc2._2)
      case _ =>
        (List[BigInt](), BigInt(1))
    }
    (bd9._1, bd9._2)
  }

  def main(args: Array[String]): Unit = {
    val points = (2 to 100 by 5) ++ (100 to 300 by 100) ++ (1000 to 10000 by 1000)
    val size = points.map(x => BigInt(x)).to[scalaList]
    val size2 = points.map(x => (x)).toList
    var ops = List[BigInt]()
    var orb = List[BigInt]()
    var valuefori = scalaList[BigInt]()
    var valuefori2 = scalaList[BigInt]()
    var valuefori3 = scalaList[BigInt]()
    
    points.foreach { i =>
      val input = i
      ops :+= {
          leon.mem.clearMemo()
          primesUntilNalloc(i)._2
       }
       orb :+= {6*i - 11}
       valuefori :+= {BigInt(i)}
    }

    dumpdata(size2, ops, orb, "primestream", "orb")
    minresults(ops, scalaList(-11, 6), List("constant", "i"), List(valuefori), size, "primestream")
  } 
}

object Stream {
  def tailalloc(thiss : RunningExample.Stream2): (RunningExample.Stream2, BigInt) = {
    val e84 = {
      assert(thiss.isInstanceOf[RunningExample.SCons1], "Cast error")
      thiss.asInstanceOf[RunningExample.SCons1]
    }.tailFun1()
    (e84._1, e84._2)
  }
}

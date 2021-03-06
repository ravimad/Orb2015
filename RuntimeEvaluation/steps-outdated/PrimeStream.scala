package PrimeStream

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
import scala.collection.mutable.{ListBuffer => scalaListBuffer}

object RunningExample {
  abstract class Bool
  
  case class True() extends Bool
  
  case class False() extends Bool
  
  
  abstract class Stream2
  
  
  case class SCons1(x318 : (BigInt, Bool), tailFun1 : () => (Stream2, BigInt)) extends Stream2
  
  
  case class SNil1() extends Stream2
  
  val primeStreamtime : (SCons1, BigInt) = (SCons1((BigInt(1), True()), () => {
    val e62 = nextElemtime(BigInt(2))
    (e62._1, BigInt(1) + e62._2)
  }), BigInt(4))
  
  def isPrimeRectime(i : BigInt, n : BigInt): (Bool, BigInt) = {
    val bd = if (i == BigInt(1)) {
      (True(), BigInt(3))
    } else {
      val c19 = BigInt(6)
      val el1 = if ({
        assert(i != BigInt(0), "Division by zero")
        n / i
      } * i == n) {
        (False(), BigInt(2) + c19)
      } else {
        val e18 = isPrimeRectime(i - BigInt(1), n)
        (e18._1, (BigInt(3) + c19) + e18._2)
      }
      (el1._1, BigInt(2) + el1._2)
    }
    (bd._1, bd._2)
  }
  
  def isPrimeNumtime(n : BigInt): (Bool, BigInt) = {
    val e57 = isPrimeRectime(n - BigInt(1), n)
    (e57._1, BigInt(2) + e57._2)
  }
  
  def nextElemtime(i : BigInt): (Stream2, BigInt) = {
    val e38 = isPrimeNumtime(i)
    val ir5 = BigInt(1) + i
    (SCons1((i, e38._1), () => {
      val e44 = nextElemtime(ir5)
      (e44._1, BigInt(1) + e44._2)
    }), BigInt(5) + e38._2)
  }
  
  def isPrimeStime(s : Stream2, i : BigInt): (Boolean, BigInt) = {
    val bd2 = s match {
      case SNil1() =>
        (true, BigInt(2))
      case SCons1(x, tfun1) =>
        val temp1 = () => {
          val e34 = nextElemtime(i)
          (e34._1, BigInt(1) + e34._2)
        }
        (tfun1 == temp1, BigInt(7))
    }
    (bd2._1, bd2._2)
  }
  
  def primesUntilNtime(n : BigInt): (List[BigInt], BigInt) = {
    val e52 = takeRectime(BigInt(0), n - BigInt(2), primeStreamtime._1)
    (e52._1, BigInt(3) + e52._2)
  }
  
  def takeRectime(i : BigInt, n : BigInt, s : Stream2): (List[BigInt], BigInt) = {
    val bd9 = s match {
      case c13 @ SCons1((x, b), _) =>
        val mc2 = if (i < n) {
          val lr = lookup[Stream2](List(4889, c13))
          val e70 = if (lr._1) {
            (lr._2, BigInt(1))
          } else {
            val e69 = Stream.tailtime(c13)
            (update[Stream2](List(4889, c13), e69._1), BigInt(3) + e69._2)
          }
          val e71 = takeRectime(BigInt(1) + i, n, e70._1)
          val r167 = if (b == True()) {
            (Cons[BigInt](x, e71._1), BigInt(4))
          } else {
            (e71._1, BigInt(3))
          }
          (r167._1, ((BigInt(4) + r167._2) + e71._2) + e70._2)
        } else {
          (List[BigInt](), BigInt(3))
        }
        (mc2._1, BigInt(6) + mc2._2)
      case _ =>
        (List[BigInt](), BigInt(5))
    }
    (bd9._1, bd9._2)
  }

  def main(args: Array[String]): Unit = {
    val points = (2 to 100 by 5) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    val size = points.map(x => BigInt(x)).to[scalaListBuffer]
    val size2 = points.map(x => (x)).toList
    var ops = List[BigInt]()
    var orb = List[BigInt]()
    var ops2 = List[BigInt]()
    var orb2 = List[BigInt]()
    var valuefori = scalaListBuffer[BigInt]()
    var valuefori2 = scalaListBuffer[BigInt]()


    points.foreach { i =>
      val input = i
      ops :+= {
        5*i*i + 28
        // 16*i*i -52
        //   leon.mem.clearMemo()
        //   primesUntilNtime(i)._2
       }
       ops2 :+= {primesUntilNtime(i)._2}
       orb :+= {16*i*i + 32}
       orb2 :+= {15*i - 18}
       valuefori2 :+= {BigInt(i*i)}
       valuefori :+= {BigInt(i)}
    }
    dumpdata(size2, ops, orb, "primesUntilN", "orb")
    dumpdata(size2, ops2, orb2, "primesUntilN2", "orb")
    minresults(ops, scalaListBuffer(28, 16), List("constant", "i*i"), List(valuefori2), size, "primestream")
    minresults(ops2, scalaListBuffer(-18, 15), List("constant", "i"), List(valuefori), size, "primestream2")

  }  
}

object Stream {
  def tailtime(thiss : RunningExample.Stream2): (RunningExample.Stream2, BigInt) = {
    val e84 = {
      assert(thiss.isInstanceOf[RunningExample.SCons1], "Cast error")
      thiss.asInstanceOf[RunningExample.SCons1]
    }.tailFun1()
    (e84._1, BigInt(5) + e84._2)
  }
}

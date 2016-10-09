package WeightedScheduling

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.runtimeDriver._
import scala.collection.mutable.{ListBuffer => scalaList}
import scala.collection.immutable.{List => scalaimmList}

object WeightedSched {
  abstract class IList
  
  case class Cons(x : BigInt, tail : IList) extends IList
  
  case class Nil() extends IList
  
  var jobs = Array[(BigInt, BigInt, BigInt)]()
  
  def jobInfotime(i : BigInt): ((BigInt, BigInt, BigInt), BigInt) = ((jobs(i.toInt), 1) : ((BigInt, BigInt, BigInt), BigInt))

  var p = Array[BigInt]()

  def prevCompatibleJobtime(i : BigInt): (BigInt, BigInt) = ((p(i.toInt), 1) : (BigInt, BigInt))
  
  @invisibleBody
  @invstate
  @memoize
  def schedtime(jobIndex : BigInt): (BigInt, BigInt) = {
    val e31 = jobInfotime(jobIndex)
    val e81 = e31._1._3
    val r162 = if (jobIndex == BigInt(0)) {
      (e81, BigInt(2))
    } else {
      val e66 = jobIndex - BigInt(1)
      val lr1 = lookup[BigInt](List(4869, e66))
      val ir2 = if (lr1._1) {
        (lr1._2, BigInt(2))
      } else {
        val e36 = schedtime(e66)
        (update[BigInt](List(4869, e66), e36._1), BigInt(4) + e36._2)
      }
      val e38 = prevCompatibleJobtime(jobIndex)
      val e71 = e38._2
      val e70 = e38._1
      val lr2 = lookup[BigInt](List(4869, e70))
      val ir3 = if (lr2._1) {
        (lr2._2, BigInt(1) + e71)
      } else {
        val e40 = schedtime(e70)
        (update[BigInt](List(4869, e70), e40._1), (BigInt(3) + e40._2) + e71)
      }
      val ir4 = (e81 + ir3._1, BigInt(1))
      val c10 = (ir4._1 >= ir2._1, BigInt(1))
      val r159 = if (ir4._1 >= ir2._1) {
        (ir4._1, BigInt(1) + c10._2)
      } else {
        (ir2._1, BigInt(1) + c10._2)
      }
      (r159._1, ((BigInt(3) + r159._2) + ir3._2) + ir2._2)
    }
    (r162._1, (BigInt(1) + r162._2) + e31._2)
  }
  
  @invisibleBody
  def invoketime(jobIndex : BigInt): (BigInt, BigInt) = {
    val lr = lookup[BigInt](List(4869, jobIndex))
    val bd = if (lr._1) {
      (lr._2, BigInt(1))
    } else {
      val e15 = schedtime(jobIndex)
      (update[BigInt](List(4869, jobIndex), e15._1), BigInt(3) + e15._2)
    }
    (bd._1, bd._2)
  }
  
  @invisibleBody
  def schedBUtime(jobi : BigInt): (IList, BigInt) = {
    val bd1 = if (jobi == BigInt(0)) {
      val e17 = invoketime(jobi)
      (Cons(e17._1, Nil()), BigInt(5) + e17._2)
    } else {
      val e23 = schedBUtime(jobi - BigInt(1))
      val e25 = invoketime(jobi)
      (Cons(e25._1, e23._1), (BigInt(6) + e25._2) + e23._2)
    }
    (bd1._1, bd1._2)
  }


  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (0 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)

    jobs = Array[(BigInt, BigInt, BigInt)]()
    jobs :+= {(BigInt(0), BigInt(0), BigInt(0))}
    (1 to 10001).foreach { n =>
      jobs :+= {(BigInt(n), BigInt(n + 2), BigInt(n))}
    }

    p = Array[BigInt]()
    p :+= {BigInt(0)}
    p :+= {BigInt(0)}
    (2 to 10001).foreach { n =>
      p :+= {BigInt(n - 2)}
    }

    val size = points.map(x => (x)).toList
    val size2 = points.map(x => BigInt(x)).to[scalaList]
    
    var orb = List[BigInt]()
    var ops = List[BigInt]()
    points.foreach { i =>
      val input = i
      ops :+= { 20*i+12
          // leon.mem.clearMemo()
          // schedBUtime(input)._2
      }
      orb :+= {20*i+ 19}
    }
    dumpdata(size, ops, orb, "wsched", "orb")
    minresults(ops, scalaList(19, 20), List("constant", "jobi"), List(size2), size2, "wsched")
  }  
  
}

object IList {
  
}

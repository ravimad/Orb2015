package FibonacciMemoized

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.runtimeDriver._
import scala.collection.mutable.{ListBuffer => scalaList}

object FibMem {
  abstract class IList
  
  case class Cons(x : BigInt, tail : IList) extends IList
  
  case class Nil() extends IList

  @memoize
  def fibRectime(n : BigInt): (BigInt, BigInt) = {
    val bd = if (n <= BigInt(2)) {
      (BigInt(1), BigInt(2))
    } else {
      val e26 = n - BigInt(1)
      val lr = lookup[BigInt](List(4814, e26))
      val e18 = if (lr._1) {
        (lr._2, BigInt(2))
      } else {
        val e17 = fibRectime(e26)
        (update[BigInt](List(4814, e26), e17._1), BigInt(4) + e17._2)
      }
      val e30 = n - BigInt(2)
      val lr1 = lookup[BigInt](List(4814, e30))
      val e23 = if (lr1._1) {
        (lr1._2, BigInt(2))
      } else {
        val e22 = fibRectime(e30)
        (update[BigInt](List(4814, e30), e22._1), BigInt(4) + e22._2)
      }
      (e18._1 + e23._1, (BigInt(3) + e23._2) + e18._2)
    }
    (bd._1, bd._2)
  }
  
  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (0 to 20 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    
    val size = points.map(x => BigInt(x)).to[scalaList]
    
    var ops = List[BigInt]()
    points.foreach { i =>
      val input = i
      ops :+= {
          leon.mem.clearMemo()
          fibRectime(input)._2
      }
    }

    minresults(ops, scalaList(2, 9), List("constant", "i"), List(size), size, "fibmem")
  }  
}

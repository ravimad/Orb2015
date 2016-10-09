package FibonacciMemoizedalloc

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._

object FibMem {
  abstract class IList
  
  case class Cons(x : BigInt, tail : IList) extends IList
  
  case class Nil() extends IList
  
  @memoize
  def fibRecalloc(n : BigInt): (BigInt, BigInt) = {
    val bd = if (n <= BigInt(2)) {
      (BigInt(1), BigInt(0))
    } else {
      val e26 = n - BigInt(1)
      val lr = lookup[BigInt](List(4813, e26))
      val e18 = if (lr._1) {
        (lr._2, BigInt(0))
      } else {
        val e17 = fibRecalloc(e26)
        (update[BigInt](List(4813, e26), e17._1), e17._2)
      }
      val e30 = n - BigInt(2)
      val lr1 = lookup[BigInt](List(4813, e30))
      val e23 = if (lr1._1) {
        (lr1._2, BigInt(0))
      } else {
        val e22 = fibRecalloc(e30)
        (update[BigInt](List(4813, e30), e22._1), e22._2)
      }
      (e18._1 + e23._1, e23._2 + e18._2)
    }
    (bd._1, bd._2)
  }
  
}

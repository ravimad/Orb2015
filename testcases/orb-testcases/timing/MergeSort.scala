import leon._
import lang._
import invariant._
import instrumentation._

import annotation._

/**
 * An implementation of a (conventional) top-down mergesort algorithm.
 * The proof uses a nontrivial axiom of nlogn (see nlognAxiom)
 */
object MergeSort {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List
  
  @invisibleBody
  def log(x: BigInt): BigInt = {
    require(x >= 0)
    if (x <= 1) BigInt(0)
    else {      
      BigInt(1) + log(x / 2)
    }
  } ensuring (_ >= 0)
  
  @invisibleBody
  def nlogn(x: BigInt): BigInt = {
    require(x >= 0)
    x * log(x)
  } ensuring(_ >= 0)

  /** 
   * An axiom of nlogn: |_n/2_|log|_n/2_| + |n/2|log|n/2| <= nlogn - |_n/2_|
   * Proof of this Axiom: 
   *   LHS <= |_n/2_|log|_n/2_| + |n/2|(log|_n/2_| + 1)  
   *   		 = (|_n/2_| + |n/2|)log|_n/2_| + |n/2| 					// this requires a bit of nonlinear reasoning and hence cannot be proven by the system
   *   		 = nlog|_n/2_| + |n/2|
   *   		 <= n(log n - 1) + |n/2|
   *   		 = nlogn  - n + |n/2|
   *   		 = RHS 
   */
  @library
  def nlognAxiom(n: BigInt): Boolean = {
    require(n >= 0)
    val flrnby2 = n / 2
    val clnby2 = n - n / 2
    (nlogn(flrnby2) + nlogn(clnby2)) <= (nlogn(n) - flrnby2)
  } holds

  def size(list: List): BigInt = {
    list match {
      case Nil()       => BigInt(0)
      case Cons(x, xs) => 1 + size(xs)
    }
  } ensuring (_ >= 0)

  @invisibleBody
  def split(l: List, n: BigInt): (List, List) = {
    require(n >= 0 && n <= size(l))
    if (n <= 0) (Nil(), l)
    else
      l match {
        case Nil() => (Nil(), l)
        case Cons(x, xs) => {
          if (n == 1) (Cons(x, Nil()), xs)
          else {
            val (fst, snd) = split(xs, n - 1)
            (Cons(x, fst), snd)
          }
        }
      }
  } ensuring (res => size(res._2) == size(l) - n && size(res._1) == n && tmpl((a, b) => steps <= a * n + b))

  @invisibleBody
  def merge(aList: List, bList: List, totsz: BigInt): List = {
    require(totsz == size(aList) + size(bList))
    bList match {
      case Nil() => aList
      case Cons(x, xs) =>
        aList match {
          case Nil() => bList
          case Cons(y, ys) =>
            if (y < x)
              Cons(y, merge(ys, bList, totsz - 1))
            else
              Cons(x, merge(aList, xs, totsz - 1))
        }
    }
  } ensuring (res => totsz == size(res) && steps <= ? * totsz + ?)

  def mergeSort(list: List, sz: BigInt): List = {
    require(sz == size(list) && nlognAxiom(sz))
    list match {
      case Cons(x, Nil()) => list
      case Cons(_, Cons(_, _)) =>
        val lby2 = sz / 2
        val (fst, snd) = split(list, lby2)
        val fsort = mergeSort(fst, lby2)
        val ssort = mergeSort(snd, sz - lby2)        
        merge(fsort, ssort, sz)
      case _ => list
    }
  } ensuring(res => size(res) == sz && steps <= ? * nlogn(sz) + ?)
}

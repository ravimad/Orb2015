import leon._
import invariant._
import instrumentation._
import lang._
import annotation._

object QuickSort {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  def size(l: List): BigInt = {
    l match {
      case Nil()       => BigInt(0)
      case Cons(x, xs) => 1 + size(xs)
    }
  } ensuring(_ >= 0)

  case class Triple(fst: List, snd: List, trd: List)

  @invisibleBody
  def append(aList: List, bList: List): List = {
    aList match {
      case Nil()       => bList
      case Cons(x, xs) => Cons(x, append(xs, bList))
    }
  } ensuring (res => size(res) == size(aList) + size(bList) && tmpl((a, b) => steps <= a * size(aList) + b))

  @invisibleBody
  def partition(n: BigInt, l: List): Triple = (l match {
    case Nil() => Triple(Nil(), Nil(), Nil())
    case Cons(x, xs) => {
      val t = partition(n, xs)
      if (n < x) Triple(t.fst, t.snd, Cons(x, t.trd))
      else if (n == x) Triple(t.fst, Cons(x, t.snd), t.trd)
      else Triple(Cons(x, t.fst), t.snd, t.trd)
    }
  }) ensuring (res => (size(l) == size(res.fst) + size(res.snd) + size(res.trd)) && tmpl((a, b) => steps <= a * size(l) + b))

  /**
   * Proof of this axiom:
   * (n + m)^2 < s^2
   * => n * n + m * m < (s * s - 2 * (n * m))
   * Also, 2 * (n*m) >= n + m (for +ve n and m) 
   * This is easy to see when n or m is 1. Say n > 1 and m > 1. WLOG say n >=m, n * m in this case is n + ... + n (m times) and is at least two times. Therefore, we have  n * m = n + n + ... >= n + n >= n + m.
   * Also, 2 * (n*m) >= n + m  holds if n = 0 and m = 0
   * Therefore, n * n + m * m < s * s - (n + m)  if  n and m are +ve or both are zero
   * Now, say one of n or m is zero. WLOG say n is non-zero i.e, n >= 1 and m is zero
   * In this case we know,  s > n therefore s >= 2
   * LHS = n * n + m * m 
   * 		 = n * n (since m is zero)
   * RHS = s * s - (n + m)
   * 		 = s * s - n 
   * 		 = s * (s - 1) + s - n 
   * 		 > s * (s - 1) 
   * 		 >= s * n 
   * 		 >= LHS
   */
  @library  
  def multAxiom(n: BigInt, m: BigInt, s: BigInt): Boolean = {
    require(n >= 0 && m >= 0 && n + m < s)
    n * n + m * m < (s * s - (n + m)) 
  } holds

  def quickSort(l: List): List = {
    require {
      l match {
        case Cons(x, xs) =>
          val t = partition(x, xs)
          multAxiom(size(t.fst), size(t.trd), size(l))
        case _ => true
      }
    }
    l match {
      case Nil()          => Nil()
      case Cons(x, Nil()) => l
      case Cons(x, xs) => {
        val t = partition(x, xs)
        append(append(quickSort(t.fst), Cons(x, t.snd)), quickSort(t.trd))
      }
      case _ => l
    }
  } ensuring (res => size(l) == size(res) && tmpl((a, b, c, d) => steps <= a * (size(l) * size(l)) + c * size(l) + d))
}


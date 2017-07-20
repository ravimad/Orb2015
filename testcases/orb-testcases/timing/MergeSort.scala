import leon._
import lang._
import invariant._
import instrumentation._

import annotation._

/**
 * An implementation of a (conventional) top-down mergesort algorithm.
 * The proof uses a nontrivial axiom of nlogn (see nlognAxiom).
 * Requires running it with --assumepreInf option
 */
object MergeSort {
  import Arithmetic._
  
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

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
  } ensuring (res => size(res._2) == size(l) - n && size(res._1) == n && steps <= ? * n + ?)

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
  } ensuring (res => size(res) == sz && steps <= ? * nlogn(sz) + ?)
}

/**
 * The following is the proof of the logAxiom.
 * It is provable with stainless but not currently with Leon.
 * We need to use --assumepre since the asserts are encoded using a function with a precondition
 */
@library
object Arithmetic {

  /**
   * Computes floor(log(x)) for all x >= 1
   */
  def log(x: BigInt): BigInt = {
    require(x >= 0)

    if (x <= 1) BigInt(0)
    else 1 + log(x / 2)

  } ensuring (_ >= 0)

  /**
   * Computes x * log(x)
   */
  @invisibleBody
  def nlogn(x: BigInt): BigInt = {
    require(x >= 0)

    x * log(x)

  } ensuring (_ >= 0)

  @traceInduct
  def logLemma1(b: BigInt): Boolean = {
    log(b + 1) <= log(b) + 1
  } holds

  /**
   * log(ceil(n/2)) <= log(floor(n/2)) + 1
   */
  def logLemma2(n: BigInt) = {
    require(n >= 0)

    val flrnby2 = n / 2
    val clnby2 = n - n / 2

    if (clnby2 != flrnby2) {
      assertI(clnby2 == flrnby2 + 1)
      assertI(logLemma1(flrnby2))
    }
    log(clnby2) <= log(flrnby2) + 1
  } holds

  /**
   * log(floor(n/2)) <= log(n) - 1
   */
  def logLemma3(n: BigInt) = {
    require(n >= 2)

    log(n / 2) <= log(n) - 1
  } holds

  /**
   * mult monotonicity
   */
  def multiplySmaller(a: BigInt, b: BigInt, c: BigInt) = {
    require(0 <= a && a <= b && 0 < c)
    c * a <= c * b
  } holds

  /**
   * An axiom of nlogn: |_n/2_|log|_n/2_| + |n/2|log|n/2| <= nlogn - |_n/2_|
   * Proof of this Axiom:
   *   LHS <= |_n/2_|log|_n/2_| + |n/2|(log|_n/2_| + 1)
   *   		 = (|_n/2_| + |n/2|)log|_n/2_| + |n/2|
   *   		 = nlog|_n/2_| + |n/2|
   *   		 <= n(log n - 1) + |n/2|
   *   		 = nlogn  - n + |n/2|
   *   		 = RHS
   */  
   def nlognAxiom(n: BigInt): Boolean = {
    require(0 <= n)    
    @invisibleBody
    def proofHints(n: BigInt): Unit =  {
      require(0 <= n)
      if (n <= 1) {
        assertI(nlognLemma2(n))
      } else {
        assertI(nlognLemma1(n))
      }
    }
    val flrnby2 = n / 2
    val clnby2 = n - n / 2
    
    val _ = proofHints(n)
    (nlogn(flrnby2) + nlogn(clnby2) <= nlogn(n) - flrnby2)
  } holds
  
  // proof for the part where n >= 2
  def nlognLemma1(n: BigInt): Boolean = {
    require(n >= 2)
    val flrnby2 = n / 2
    val clnby2 = n - (n / 2)

    assertI(logLemma2(n))
    assertI(log(clnby2) <= log(flrnby2) + 1)
    assertI(nlogn(flrnby2) + nlogn(clnby2) <= nlogn(flrnby2) + clnby2 * log(clnby2))
    assertI(nlogn(flrnby2) + nlogn(clnby2) <= nlogn(flrnby2) + clnby2 * (log(flrnby2) + 1))
    assertI(nlogn(flrnby2) + nlogn(clnby2) <= nlogn(flrnby2) + clnby2 * log(flrnby2) + clnby2)
    assertI(nlogn(flrnby2) + nlogn(clnby2) <= flrnby2 * log(flrnby2) + clnby2 * log(flrnby2) + clnby2)
    assertI(nlogn(flrnby2) + nlogn(clnby2) <= (flrnby2 + clnby2) * log(flrnby2) + clnby2)
    assertI(nlogn(flrnby2) + nlogn(clnby2) <= n * log(flrnby2) + clnby2)

    assertI(logLemma3(n))
    assertI(multiplySmaller(log(flrnby2), log(n) - 1, n))
    assertI(n * log(flrnby2) <= n * (log(n) - 1))

    assertI(nlogn(flrnby2) + nlogn(clnby2) <= n * (log(n) - 1) + clnby2)
    assertI(nlogn(flrnby2) + nlogn(clnby2) <= n * log(n) - n + clnby2)

    nlogn(flrnby2) + nlogn(clnby2) <= n * log(n) - flrnby2
  } holds

  // proof for the part where 0 <= n <= 1
  def nlognLemma2(n: BigInt): Boolean = {
    require(0 <= n && n <= 1)
    val flrnby2 = n / 2
    val clnby2 = n - n / 2

    nlogn(flrnby2) + nlogn(clnby2) <= nlogn(n) - flrnby2
  } holds 
  
  def assertI(b: Boolean): Unit = {
    require(b)
  }

}

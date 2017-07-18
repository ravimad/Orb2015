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

  @library
  def multAxiom(n: BigInt, m: BigInt, s: BigInt): Boolean = {
    require(n >= 0 && m >= 0 && s >= 0)
    (n + m < s) ==> (n * n + m * m < s * s)
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


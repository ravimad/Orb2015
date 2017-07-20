import leon._
import invariant._
import instrumentation._
import annotation._
import lang._

object HeapSort {
  import LogExpAxioms._

  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  sealed abstract class Heap
  case class Leaf() extends Heap
  case class Node(rk: BigInt, value: BigInt, left: Heap, right: Heap) extends Heap

  def heapSize(t: Heap): BigInt = {
    t match {
      case Leaf()           => BigInt(0)
      case Node(_, v, l, r) => heapSize(l) + 1 + heapSize(r)
    }
  } ensuring (res => res >= 0)

  def sizeHeightPropWeak(t: Heap): Boolean = {
    require(hasLeftistProperty(t))
    (t match {
      case Leaf()           => true
      case Node(_, v, l, r) => sizeHeightPropWeak(l) && sizeHeightPropWeak(r)
    }) &&
      twopower(rightHeight(t)) <= heapSize(t) + 1
  } holds

  /**
   * Proof of the property that "rightHeight(t) <= log(size(t)+1)"
   */
  def sizeHeightProp(t: Heap): Boolean = {
    require(hasLeftistProperty(t))
    @invisibleBody
    def proofAxioms(t: Heap): Boolean = {
      (sizeHeightPropWeak(t) &&
        logTwopowerAxiom(rightHeight(t)) &&
        logMonotone(heapSize(t) + 1, twopower(rightHeight(t))))
    }
    proofAxioms(t) && rightHeight(t) <= log(heapSize(t) + 1)
  } holds

  def rightHeight(h: Heap): BigInt = {
    h match {
      case Leaf()           => BigInt(0)
      case Node(_, _, _, r) => rightHeight(r) + 1
    }
  } ensuring (res => res >= 0)

  def rank(h: Heap): BigInt = h match {
    case Leaf()            => 0
    case Node(rk, _, _, _) => rk
  }

  def hasLeftistProperty(h: Heap): Boolean = (h match {
    case Leaf()           => true
    case Node(_, _, l, r) => hasLeftistProperty(l) && hasLeftistProperty(r) && rightHeight(l) >= rightHeight(r) && (rank(h) == rightHeight(h))
  })

  @invisibleBody
  def merge(h1: Heap, h2: Heap): Heap = {
    require(hasLeftistProperty(h1) && hasLeftistProperty(h2))
    h1 match {
      case Leaf() => h2
      case Node(_, v1, l1, r1) => h2 match {
        case Leaf() => h1
        case Node(_, v2, l2, r2) =>
          if (v1 > v2)
            makeT(v1, l1, merge(r1, h2))
          else
            makeT(v2, l2, merge(h1, r2))
      }
    }
  } ensuring (res => hasLeftistProperty(res) && heapSize(res) == heapSize(h1) + heapSize(h2) &&
    steps <= ? * rightHeight(h1) + ? * rightHeight(h2) + ?)

  def makeT(value: BigInt, left: Heap, right: Heap): Heap = {
    require(hasLeftistProperty(left) && hasLeftistProperty(right))
    if (rank(left) >= rank(right))
      Node(rank(right) + 1, value, left, right)
    else
      Node(rank(left) + 1, value, right, left)
  }

  @invisibleBody
  def insert(element: BigInt, heap: Heap): Heap = {
    require(hasLeftistProperty(heap))

    @invisibleBody
    def insInner(e: BigInt, h: Heap): Heap = {
      require(hasLeftistProperty(h) && sizeHeightProp(heap))

      merge(Node(1, e, Leaf(), Leaf()), h)

    } ensuring (res => heapSize(res) == heapSize(h) + 1 &&
      steps <= ? * rightHeight(h) + ?)

    insInner(element, heap)

  } ensuring (res => hasLeftistProperty(res) && heapSize(res) == heapSize(heap) + 1 &&
    steps <= ? * log(heapSize(heap) + 1) + ?)

  def findMax(h: Heap): BigInt = {
    require(h != Leaf())
    h match {
      case Node(_, m, _, _) => m
    }
  }

  @invisibleBody
  def removeMax(h: Heap): Heap = {
    require(h != Leaf() && hasLeftistProperty(h))
    @invisibleBody
    def remInner(h: Heap): Heap = {
      require(h != Leaf() && hasLeftistProperty(h)
        &&
        (h match {
          case Node(_, _, l, r) => sizeHeightProp(l) && logMonotone(heapSize(h) + 1, heapSize(l) + 1)
        }))
      h match {
        case Node(_, _, l, r) => merge(l, r)
      }
    } ensuring (res => hasLeftistProperty(res) && heapSize(res) == heapSize(h) - 1 && steps <= ? * log(heapSize(h) + 1) + ?)

    remInner(h)
  } ensuring (res => hasLeftistProperty(res) && heapSize(res) == heapSize(h) - 1 && steps <= ? * log(heapSize(h) + 1) + ?)

  def listSize(l: List): BigInt = (l match {
    case Nil()       => BigInt(0)
    case Cons(_, xs) => 1 + listSize(xs)
  }) ensuring (_ >= 0)

  @invisibleBody
  def removeElements(h: Heap): List = {
    require(hasLeftistProperty(h))
    h match {
      case Leaf()           => Nil()
      case Node(_, m, _, _) => Cons(m, removeElements(removeMax(h)))
    }
  } ensuring { res =>
    heapSize(h) == listSize(res) &&
      steps <= ? * (heapSize(h) * log(heapSize(h) + 1)) + ? * heapSize(h) + ?
  }

  @invisibleBody
  def buildHeap(l: List): Heap = {
    l match {
      case Nil()       => Leaf()
      case Cons(x, xs) => insert(x, buildHeap(xs))
    }
  } ensuring (res => hasLeftistProperty(res) &&
    heapSize(res) == listSize(l) &&
    steps <= ? * (listSize(l) * log(listSize(l) + 1)) + ? * log(listSize(l) + 1) + ?)

  def sort(l: List): List = {
    removeElements(buildHeap(l))
  } ensuring (res =>
    steps <= ? * (listSize(l) * log(listSize(l) + 1)) + ? * log(listSize(l) + 1) + ?)
}

object LogExpAxioms {
  @monotonic
  def twopower(x: BigInt): BigInt = {
    require(x >= 0)
    if (x <= 0) BigInt(1)
    else
      2 * twopower(x - 1)
  } ensuring (_ >= 1)

  // uses integer division and equivalent to floor(log(x))
  @monotonic
  def log(x: BigInt): BigInt = {
    require(x >= 1)
    if (x <= 1) BigInt(0)
    else 1 + log(x / 2)
  } ensuring (_ >= 0)

  def logMonotone(x: BigInt, y: BigInt): Boolean = {
    require(x >= y && y >= 1)
    (if (y <= 1) true else logMonotone(x / 2, y / 2)) &&
      (log(x) >= log(y))
  } holds

  /**
   * Proof of the axiom: log(2^x) = x
   */
  def logTwopowerAxiom(x: BigInt): Boolean = {
    require(x >= 0)
    (if (x <= 0) true
    else logTwopowerAxiom(x - 1)) && log(twopower(x)) == x
  } holds
}
package orb

import leon._
import invariant._
import instrumentation._

object AmortizedQueue {
  sealed abstract class MyList {
    val size: BigInt = this match {
      case Nil()       => 0
      case Cons(_, xs) => 1 + xs.size
    }
  }
  case class Cons(head: BigInt, tail: MyList) extends MyList
  case class Nil() extends MyList

  def length(l: MyList): BigInt = {
    l match {
      case Nil()       => BigInt(0)
      case Cons(_, xs) => 1 + length(xs)
    }
  } ensuring(res => res >= 0 && time <= ? * l.size + ?)

  def concat(l1: MyList, l2: MyList): MyList = (l1 match {
    case Nil()       => l2
    case Cons(x, xs) => Cons(x, concat(xs, l2))

  }) ensuring (res => res.size == l1.size + l2.size && time <= ? * l1.size + ?)

  def reverseRec(l1: MyList, l2: MyList): MyList = (l1 match {
    case Nil()       => l2
    case Cons(x, xs) => reverseRec(xs, Cons(x, l2))
  }) ensuring (res => l1.size + l2.size == res.size && time <= ? * l1.size + ?)

  def MyListRev(l: MyList): MyList = {
    reverseRec(l, Nil())
  } ensuring (res => l.size == res.size && time <= ? * l.size + ?)

  def removeLast(l: MyList): MyList = {
    require(l != Nil())
    l match {
      case Cons(x, Nil()) => Nil()
      case Cons(x, xs)    => Cons(x, removeLast(xs))
      case _              => Nil()
    }
  } ensuring (res => res.size <= l.size && tmpl((a, b) => time <= a * l.size + b))

  case class Queue(front: MyList, rear: MyList) {
    def qsize: BigInt = front.size + rear.size

    def asMyList: MyList = concat(front, MyListRev(rear))

    def isAmortized: Boolean = length(front) >= length(rear)

    def isEmpty: Boolean = this match {
      case Queue(Nil(), Nil()) => true
      case _                   => false
    }

    def amortizedQueue(front: MyList, rear: MyList): Queue = {
      if (length(rear) <= length(front))
        Queue(front, rear)
      else
        Queue(concat(front, MyListRev(rear)), Nil())
    }

    def enqueue(elem: BigInt): Queue = ({
      amortizedQueue(front, Cons(elem, rear))
    }) ensuring (_ => time <= ? * qsize + ?)

    def dequeue: Queue = {
      require(isAmortized && !isEmpty)
      front match {
        case Cons(f, fs) => amortizedQueue(fs, rear)
        case _           => Queue(Nil(), Nil())
      }
    } ensuring (_ => time <= ? * qsize + ?)

    def head: BigInt = {
      require(isAmortized && !isEmpty)
      front match {
        case Cons(f, _) => f
      }
    }

    def reverse: Queue = { // this lets the queue perform deque operation (but they no longer have efficient constant time amortized bounds)
      amortizedQueue(rear, front)
    }
  }
}

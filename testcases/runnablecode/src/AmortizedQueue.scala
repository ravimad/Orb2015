import leon._
import leon.invariant._
import leon.instrumentation._

object AmortizedQueue {
  abstract class MyList
  
  case class Cons(head : BigInt, tail : MyList) extends MyList
  
  case class Nil() extends MyList
  
  case class Queue(front : MyList, rear : MyList)
  
  def lengthalloc(l : MyList): (BigInt, BigInt) = {
    val bd1 = l match {
      case Nil() =>
        (BigInt(0), BigInt(0))
      case Cons(_, xs) =>
        val e32 = lengthalloc(xs)
        (BigInt(1) + e32._1, e32._2)
    }
    bd1
  }
  
  def concatalloc(l1 : MyList, l2 : MyList): (MyList, BigInt) = {
    val bd4 = l1 match {
      case Nil() =>
        (l2, BigInt(0))
      case Cons(x, xs) =>
        val e48 = concatalloc(xs, l2)
        (Cons(x, e48._1), BigInt(1) + e48._2)
    }
    bd4
  }
  
  def reverseRecalloc(l1 : MyList, l2 : MyList): (MyList, BigInt) = {
    val bd7 = l1 match {
      case Nil() =>
        (l2, BigInt(0))
      case Cons(x, xs) =>
        val e63 = reverseRecalloc(xs, Cons(x, l2))
        (e63._1, BigInt(1) + e63._2)
    }
    bd7
  }
  
  def MyListRevalloc(l : MyList): (MyList, BigInt) = {
    val e43 = reverseRecalloc(l, Nil())
    (e43._1, BigInt(1) + e43._2)
  }
  
  def removeLastalloc(l : MyList): (MyList, BigInt) = {
    val bd5 = l match {
      case Cons(x, Nil()) =>
        (Nil(), BigInt(1))
      case Cons(x, xs) =>
        val e52 = removeLastalloc(xs)
        (Cons(x, e52._1), BigInt(1) + e52._2)
      case _ =>
        (Nil(), BigInt(1))
    }
    bd5
  }
}

object MyList {
  def size(thiss : AmortizedQueue.MyList): BigInt = thiss match {
    case AmortizedQueue.Nil() =>
      BigInt(0)
    case AmortizedQueue.Cons(_, xs) =>
      BigInt(1) + size(xs)
  }
}

object Queue {
  def isAmortized(thiss : AmortizedQueue.Queue): Boolean = AmortizedQueue.lengthalloc(thiss.front)._1 >= AmortizedQueue.lengthalloc(thiss.rear)._1
  
  def amortizedQueuealloc(thiss : AmortizedQueue.Queue, front : AmortizedQueue.MyList, rear : AmortizedQueue.MyList): (AmortizedQueue.Queue, BigInt) = {
    val e28 = AmortizedQueue.lengthalloc(rear)
    val e26 = AmortizedQueue.lengthalloc(front)
    val c10 = e26._2 + e28._2
    val bd = if (e28._1 <= e26._1) {
      (AmortizedQueue.Queue(front, rear), BigInt(1) + c10)
    } else {
      val e22 = AmortizedQueue.MyListRevalloc(rear)
      val e20 = AmortizedQueue.concatalloc(front, e22._1)
      (AmortizedQueue.Queue(e20._1, AmortizedQueue.Nil()), ((BigInt(2) + c10) + e20._2) + e22._2)
    }
    bd
  }
  
  def dequeuealloc(thiss : AmortizedQueue.Queue): (AmortizedQueue.Queue, BigInt) = {
    val bd2 = thiss.front match {
      case AmortizedQueue.Cons(f, fs) =>
        val e36 = amortizedQueuealloc(thiss, fs, thiss.rear)
        e36
      case _ =>
        (AmortizedQueue.Queue(AmortizedQueue.Nil(), AmortizedQueue.Nil()), BigInt(3))
    }
    bd2
  }
  
  def qsize(thiss : AmortizedQueue.Queue): BigInt = MyList.size(thiss.front) + MyList.size(thiss.rear)
  
  def reverse(thiss : AmortizedQueue.Queue): AmortizedQueue.Queue = amortizedQueuealloc(thiss, thiss.rear, thiss.front)._1
  
  def head(thiss : AmortizedQueue.Queue): BigInt = {
    val AmortizedQueue.Cons(f, _) = thiss.front
    f
  }
  
  def isEmpty(thiss : AmortizedQueue.Queue): Boolean = thiss match {
    case AmortizedQueue.Queue(AmortizedQueue.Nil(), AmortizedQueue.Nil()) =>
      true
    case _ =>
      false
  }
  
  def enqueuealloc(thiss : AmortizedQueue.Queue, elem : BigInt): (AmortizedQueue.Queue, BigInt) = {
    val e56 = amortizedQueuealloc(thiss, thiss.front, AmortizedQueue.Cons(elem, thiss.rear))
    (e56._1, BigInt(1) + e56._2)
  }
  
  def asMyList(thiss : AmortizedQueue.Queue): AmortizedQueue.MyList = AmortizedQueue.concatalloc(thiss.front, AmortizedQueue.MyListRevalloc(thiss.rear)._1)._1

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    val size = points
    var operAlloc = List[Any]() // Keeps track of allocation

    points.foreach { i =>
      val input = {
        (1 to i).foldLeft[AmortizedQueue.MyList](AmortizedQueue.Nil()) { (f, n) =>
          AmortizedQueue.Cons(1, f)  
        }
      }
      val q = AmortizedQueue.Queue(AmortizedQueue.Nil(), input)
      operAlloc :+= (q.enqueuealloc(2))._2
    }

    val orbAlloc = size.map(x => x).toList // Keeps track of Orb predicted results

    var j = 0
    for(i <- size) {
      println(s"$i ${orbAlloc(j)}")
      j = j + 1
    }

    j = 0
    for(i <- size) {
      println(s"$i ${operAlloc(j)}")
      j = j + 1
    }


    /* Use a plotting library that will plot
    1) size -> orbTime
    2) size -> operTime
    3) size -> realTime
     */
  }
} // extra brace, just ensure `main` is inside the `object` of the benchmark

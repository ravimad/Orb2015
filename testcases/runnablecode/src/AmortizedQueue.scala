import leon._
import leon.invariant._
import leon.instrumentation._

object AmortizedQueue {
  abstract class MyList
  
  case class Cons(head : BigInt, tail : MyList) extends MyList
  
  case class Nil() extends MyList
  
  case class Queue(front : MyList, rear : MyList)
  
  def lengthtime(l : MyList): (BigInt, BigInt) = {
    val bd1 = l match {
      case Nil() =>
        (BigInt(0), BigInt(2))
      case Cons(_, xs) =>
        val e32 = lengthtime(xs)
        (BigInt(1) + e32._1, BigInt(6) + e32._2)
    }
    bd1
  }
  
  def concattime(l1 : MyList, l2 : MyList): (MyList, BigInt) = {
    val bd4 = l1 match {
      case Nil() =>
        (l2, BigInt(2))
      case Cons(x, xs) =>
        val e48 = concattime(xs, l2)
        (Cons(x, e48._1), BigInt(7) + e48._2)
    }
    bd4
  }
  
  def reverseRectime(l1 : MyList, l2 : MyList): (MyList, BigInt) = {
    val bd7 = l1 match {
      case Nil() =>
        (l2, BigInt(2))
      case Cons(x, xs) =>
        val e63 = reverseRectime(xs, Cons(x, l2))
        (e63._1, BigInt(7) + e63._2)
    }
    bd7
  }
  
  def MyListRevtime(l : MyList): (MyList, BigInt) = {
    val e43 = reverseRectime(l, Nil())
    (e43._1, BigInt(2) + e43._2)
  }
  
  def removeLasttime(l : MyList): (MyList, BigInt) = {
    val bd5 = l match {
      case Cons(x, Nil()) =>
        (Nil(), BigInt(6))
      case Cons(x, xs) =>
        val e52 = removeLasttime(xs)
        (Cons(x, e52._1), BigInt(9) + e52._2)
      case _ =>
        (Nil(), BigInt(6))
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
  def isAmortized(thiss : AmortizedQueue.Queue): Boolean = AmortizedQueue.lengthtime(thiss.front)._1 >= AmortizedQueue.lengthtime(thiss.rear)._1
  
  def amortizedQueuetime(thiss : AmortizedQueue.Queue, front : AmortizedQueue.MyList, rear : AmortizedQueue.MyList): (AmortizedQueue.Queue, BigInt) = {
    val e28 = AmortizedQueue.lengthtime(rear)
    val e26 = AmortizedQueue.lengthtime(front)
    val c10 = (BigInt(3) + e26._2) + e28._2
    val bd = if (e28._1 <= e26._1) {
      (AmortizedQueue.Queue(front, rear), BigInt(2) + c10)
    } else {
      val e22 = AmortizedQueue.MyListRevtime(rear)
      val e20 = AmortizedQueue.concattime(front, e22._1)
      (AmortizedQueue.Queue(e20._1, AmortizedQueue.Nil()), ((BigInt(5) + c10) + e20._2) + e22._2)
    }
    bd
  }
  
  def dequeuetime(thiss : AmortizedQueue.Queue): (AmortizedQueue.Queue, BigInt) = {
    val bd2 = thiss.front match {
      case AmortizedQueue.Cons(f, fs) =>
        val e36 = amortizedQueuetime(thiss, fs, thiss.rear)
        (e36._1, BigInt(7) + e36._2)
      case _ =>
        (AmortizedQueue.Queue(AmortizedQueue.Nil(), AmortizedQueue.Nil()), BigInt(6))
    }
    bd2
  }
  
  def qsize(thiss : AmortizedQueue.Queue): BigInt = MyList.size(thiss.front) + MyList.size(thiss.rear)
  
  def reverse(thiss : AmortizedQueue.Queue): AmortizedQueue.Queue = amortizedQueuetime(thiss, thiss.rear, thiss.front)._1
  
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
  
  def enqueuetime(thiss : AmortizedQueue.Queue, elem : BigInt): (AmortizedQueue.Queue, BigInt) = {
    val e56 = amortizedQueuetime(thiss, thiss.front, AmortizedQueue.Cons(elem, thiss.rear))
    (e56._1, BigInt(4) + e56._2)
  }
  
  def asMyList(thiss : AmortizedQueue.Queue): AmortizedQueue.MyList = AmortizedQueue.concattime(thiss.front, AmortizedQueue.MyListRevtime(thiss.rear)._1)._1

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    val size = points.map(x => 2*x).toList
    var operAlloc = List[Any]() // Keeps track of allocation

    points.foreach { i =>
      val input = {
        (1 to i).foldLeft[AmortizedQueue.MyList](AmortizedQueue.Nil()) { (f, n) =>
          AmortizedQueue.Cons(1, f)  
        }
      }
      val q = AmortizedQueue.Queue(input, input)
      operAlloc :+= (enqueuetime(q, 2))._2
    }

    val orbAlloc = size.map(x => 11*x + 35).toList // Keeps track of Orb predicted results

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

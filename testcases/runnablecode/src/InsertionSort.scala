import leon.invariant._
import leon.instrumentation._

object InsertionSort {
  abstract class List
  
  case class Cons(head : BigInt, tail : List) extends List
  
  case class Nil() extends List
  
  def sizealloc(l : List): (BigInt, BigInt) = {
    val bd14 = l match {
      case Cons(_, xs) =>
        val e223 = sizealloc(xs)
        (BigInt(1) + e223._1, e223._2)
      case _ =>
        (BigInt(0), BigInt(0))
    }
    bd14
  }
  
  def sortedInsalloc(e : BigInt, l : List): (List, BigInt) = {
    val bd40 = l match {
      case Cons(x, xs) =>
        val mc136 = if (x < e) {
          val e649 = sortedInsalloc(e, xs)
          (Cons(x, e649._1), BigInt(1) + e649._2)
        } else {
          (Cons(e, l), BigInt(1))
        }
        mc136
      case _ =>
        (Cons(e, Nil()), BigInt(2))
    }
    bd40
  }
  
  def sortalloc(l : List): (List, BigInt) = {
    val bd2 = l match {
      case Cons(x, xs) =>
        val e28 = sortalloc(xs)
        val e26 = sortedInsalloc(x, e28._1)
        (e26._1, e26._2 + e28._2)
      case _ =>
        (Nil(), BigInt(1))
    }
    bd2
  }

 def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    val size = points
    var operAlloc = List[Any]() // Keeps track of instrumented values

    points.foreach { i =>
      val input = {
        (1 to i).foldLeft[List](Nil()) { (f, n) =>
          Cons(1, f)
        }
      }
      operAlloc :+= sortedInsalloc(2, input)._2
    }

    val orbAlloc = size.map(x => x + 2).toList // Keeps track of Orb predicted results

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

//    println(orbAlloc)
//    println(operAlloc)
    /* Use a plotting library that will plot
    1) size -> orbAlloc
    2) size -> operAlloc
     */
  }
} // extra brace, just ensure `main` is inside the `object` of the benchmark

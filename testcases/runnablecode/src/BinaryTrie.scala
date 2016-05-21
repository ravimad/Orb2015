import leon.invariant._
import leon.instrumentation._

object BinaryTrie {
  abstract class Tree
  
  case class Leaf() extends Tree
  
  case class Node(nvalue : BigInt, left : Tree, right : Tree) extends Tree
  
  abstract class IList
  
  case class Cons(head : BigInt, tail : IList) extends IList
  
  case class Nil() extends IList
  
  def listSize(l : IList): BigInt = l match {
    case Nil() =>
      BigInt(0)
    case Cons(x, xs) =>
      BigInt(1) + listSize(xs)
  }
  
  def height(t : Tree): BigInt = t match {
    case Leaf() =>
      BigInt(0)
    case Node(x, l, r) =>
      val hl = height(l)
      val hr = height(r)
      if (hl > hr) {
        hl + BigInt(1)
      } else {
        hr + BigInt(1)
      }
  }
  
  def findalloc(inp : IList, t : Tree): (Tree, BigInt) = {
    val bd3 = inp match {
      case Nil() =>
        (t, BigInt(0))
      case Cons(x, Nil()) =>
        (t, BigInt(0))
      case Cons(x, xs @ Cons(y, _)) =>
        val mc20 = t match {
          case Leaf() =>
            (t, BigInt(0))
          case Node(v, l, r) =>
            val mc22 = if (y > BigInt(0)) {
              val e86 = findalloc(xs, l)
              e86
            } else {
              val e89 = findalloc(xs, r)
              e89
            }
            mc22
        }
        mc20
      case _ =>
        (t, BigInt(0))
    }
    bd3
  }
  
  def insertalloc(inp : IList, t : Tree): (Tree, BigInt) = {
    val bd1 = t match {
      case Leaf() =>
        val mc = inp match {
          case Nil() =>
            (t, BigInt(0))
          case Cons(x, xs) =>
            val e19 = insertalloc(xs, Leaf())
            val e124 = e19._1
            val r162 = e124 match {
              case Leaf() =>
                (Node(x, Leaf(), Leaf()), BigInt(3))
              case Node(y, _, _) =>
                val mc4 = if (y > BigInt(0)) {
                  (Node(x, e124, Leaf()), BigInt(2))
                } else {
                  (Node(y, Leaf(), e124), BigInt(2))
                }
                mc4
            }
            (r162._1, (BigInt(1) + r162._2) + e19._2)
        }
        mc
      case Node(v, l, r) =>
        val mc5 = inp match {
          case Nil() =>
            (t, BigInt(0))
          case Cons(x, Nil()) =>
            (t, BigInt(0))
          case Cons(x, xs @ Cons(y, _)) =>
            val ir1 = if (y > BigInt(0)) {
              (l, BigInt(0))
            } else {
              (r, BigInt(0))
            }
            val ir10 = ir1._1
            val r163 = if (y > BigInt(0)) {
              val e38 = insertalloc(xs, ir10)
              (Node(v, e38._1, r), BigInt(1) + e38._2)
            } else {
              val e44 = insertalloc(xs, ir10)
              (Node(v, l, e44._1), BigInt(1) + e44._2)
            }
            (r163._1, r163._2 + ir1._2)
          case _ =>
            (t, BigInt(0))
        }
        mc5
    }
    bd1
  }
  
  def createalloc(inp : IList): (Tree, BigInt) = {
    val e16 = insertalloc(inp, Leaf())
    (e16._1, BigInt(1) + e16._2)
  }
  
  def deletealloc(inp : IList, t : Tree): (Tree, BigInt) = {
    val bd2 = t match {
      case Leaf() =>
        val mc10 = inp match {
          case Nil() =>
            (Leaf(), BigInt(1))
          case Cons(x, xs) =>
            (Leaf(), BigInt(1))
        }
        mc10
      case Node(v, l, r) =>
        val mc13 = inp match {
          case Nil() =>
            (t, BigInt(0))
          case Cons(x, Nil()) =>
            val c18 = BigInt(2)
            val mc15 = if (l == Leaf() && r == Leaf()) {
              (Leaf(), BigInt(1) + c18)
            } else {
              (t, c18)
            }
            mc15
          case Cons(x, xs @ Cons(y, _)) =>
            val ir2 = if (y > BigInt(0)) {
              (l, BigInt(0))
            } else {
              (r, BigInt(0))
            }
            val e57 = deletealloc(xs, ir2._1)
            val e98 = e57._1
            val c22 = BigInt(3)
            val r165 = if (e98 == Leaf() && (y > BigInt(0) && r == Leaf() || y <= BigInt(0) && l == Leaf())) {
              (Leaf(), BigInt(1) + c22)
            } else {
              val el5 = if (y > BigInt(0)) {
                (Node(v, e98, r), BigInt(1))
              } else {
                (Node(v, l, e98), BigInt(1))
              }
              (el5._1, c22 + el5._2)
            }
            (r165._1, (r165._2 + e57._2) + ir2._2)
          case _ =>
            (t, BigInt(0))
        }
        mc13
    }
    bd2
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    val size = points.map(x => 2*x).toList
    var operAlloc = List[Any]() // Keeps track of allocation

    points.foreach { i =>
      val input = {
        (1 to i).foldLeft[IList](Nil()) { (f, n) =>
          Cons(1, f)  
        }
      }
      operAlloc :+= (insertalloc(input, Leaf()))._2
    }

    val orbAlloc = size.map(x => 1.5*x).toList // Keeps track of Orb predicted results

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
}

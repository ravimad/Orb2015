package knapsck

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.runtimeDriver._

object Knapscak {
  abstract class IList
  
  case class Cons(x : (BigInt, BigInt), tail : IList) extends IList
  
  case class Nil() extends IList
  
  @invstate
  def maxValuetime(items : IList, w : BigInt, currList : IList): (BigInt, BigInt) = {
    val bd = currList match {
      case Cons((wi, vi), tail) =>
        val e17 = maxValuetime(items, w, tail)
        val e68 = e17._1
        val c13 = BigInt(3)
        val r159 = if (wi <= w && wi > BigInt(0)) {
          val e74 = w - wi
          val lr = lookup[BigInt](List(4867, e74, items))
          val e24 = if (lr._1) {
            (lr._2, BigInt(2))
          } else {
            val e23 = knapSacktime(e74, items)
            (update[BigInt](List(4867, e74, items), e23._1), BigInt(4) + e23._2)
          }
          val ir1 = (vi + e24._1, BigInt(1) + e24._2)
          val c9 = (ir1._1 >= e68, BigInt(1))
          val r158 = if (ir1._1 >= e68) {
            (ir1._1, BigInt(1) + c9._2)
          } else {
            (e68, BigInt(1) + c9._2)
          }
          (r158._1, ((BigInt(2) + c13) + r158._2) + e24._2)
        } else {
          (e68, BigInt(1) + c13)
        }
        (r159._1, (BigInt(8) + r159._2) + e17._2)
      case Nil() =>
        (BigInt(0), BigInt(5))
    }
    (bd._1, bd._2)
  }
  
  @memoize
  def knapSacktime(w : BigInt, items : IList): (BigInt, BigInt) = {
    val bd2 = if (w == BigInt(0)) {
      (BigInt(0), BigInt(2))
    } else {
      val e39 = maxValuetime(items, w, items)
      (e39._1, BigInt(3) + e39._2)
    }
    (bd2._1, bd2._2)
  }
  
  @invisibleBody
  def invoketime(i : BigInt, items : IList): (BigInt, BigInt) = {
    val lr1 = lookup[BigInt](List(4867, i, items))
    val bd1 = if (lr1._1) {
      (lr1._2, BigInt(1))
    } else {
      val e35 = knapSacktime(i, items)
      (update[BigInt](List(4867, i, items), e35._1), BigInt(3) + e35._2)
    }
    (bd1._1, bd1._2)
  }
  
  def bottomuptime(w : BigInt, items : IList): (IList, BigInt) = {
    val bd4 = if (w == BigInt(0)) {
      val e48 = invoketime(w, items)
      (Cons((w, e48._1), Nil()), BigInt(6) + e48._2)
    } else {
      val e56 = bottomuptime(w - BigInt(1), items)
      val e60 = invoketime(w, items)
      (Cons((w, e60._1), e56._1), (BigInt(7) + e60._2) + e56._2)
    }
    (bd4._1, bd4._2)
  }
  
  def knapSackSoltime(w : BigInt, items : IList): (IList, BigInt) = {
    val e44 = bottomuptime(w, items)
    (e44._1, BigInt(1) + e44._2)
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (10 to 200 by 10) ++ (100 to 1000 by 50)// ++ (1000 to 10000 by 1000)
    val size = points.map(x => BigInt(x)).toList
    
    val ws = (100 to 900 by 100)
    val itemsizes = (100 to 900 by 100)

    import java.io.File
    import java.io.FileWriter
    import java.io.BufferedWriter

    val files = new FileWriter(s"results/3dDATA.data")
    val fileout = new BufferedWriter(files)

    ws.foreach { w =>
      itemsizes.foreach { itemsize =>
        leon.mem.clearMemo()
         val input = {
          (1 to itemsize).foldLeft[IList](Nil()) { (f, n) =>
            Cons((rand.nextInt(itemsize), rand.nextInt(itemsize)), f)  
          }
        }
        fileout.write(s"$w $itemsize ${knapSackSoltime(w, input)._2}\n")
      }
    }
    
    fileout.close()
  }  
  
}

object IList {
  
}

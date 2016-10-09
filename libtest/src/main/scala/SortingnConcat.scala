package sortnc

import leon._
import mem._
import higherorder._
import lang._
import annotation._
import instrumentation._
import invariant._
import collection._

object SortingnConcat {

  sealed abstract class LList {
    def size: BigInt = {
      this match {
        case SCons(_, t) => 1 + t.size
        case _            => BigInt(0)
      }
    }
  }

  private case class SCons(x: BigInt, tailFun: Stream) extends LList
  private case class SNil() extends LList
  private case class Stream(lfun: () => LList) {
    lazy val list: LList = lfun()
    @inline
    def size = (list*).size
  }


  def pullMin(l: List[BigInt]): List[BigInt] = {
    l match {
      case Nil() => l
      case Cons(x, xs) =>
        pullMin(xs) match {
          case Nil() => Cons(x, Nil())
          case nxs @ Cons(y, ys) =>
            if (x <= y) Cons(x, nxs)
            else Cons(y, Cons(x, ys))
        }
    }
  }

  def sort(l: List[BigInt]): LList = {
    pullMin(l) match {
      case Cons(x, xs) =>
        // here, x is the minimum
        SCons(x, Stream(() => sort(xs))) // sorts lazily only if needed
      case _ =>
        SNil()
    }
  }

  def concat(l1: List[BigInt], l2: LList) : LList = {
    l1 match {
      case Cons(x, xs) => SCons(x, Stream(() => concat(xs, l2)))
      case Nil() => SNil()
    }
  } 

  def kthMin(l: Stream, k: BigInt): BigInt = {
    l.list match {
      case SCons(x, xs) =>
        if (k == 1) x
        else
          kthMin(xs, k - 1)
      case SNil() => BigInt(0)
    }
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    import scala.math.BigInt
    import stats._
    import collection._
    import scala.util.Random
    import java.lang.management._
    import scala.collection.JavaConversions._
    import java.lang.management._

    val rand = Random

    val nooftimes = (1 to 100000)
    val length = (1000 to 10000 by 1000)
    

    length.foreach { i =>
      var totalTime = 0L
      var ptotalTime = 0L
      val tinput = {
        (1 to i).foldLeft[List[BigInt]](Nil()) { (f, n) =>
          Cons(n, f)  
        }
      }
      val input = sort(tinput) match {
        case SCons(_, t) => t
        case SNil() => Stream(()=>SNil())
      }
      nooftimes.foreach { _ =>
        var t1 = System.nanoTime()
        val x = sort(tinput) match {
          case SCons(_, t) => t
          case SNil() => Stream(()=>SNil())
        }
        var gct1 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
        var r = kthMin(x, 10)
        var gct2 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
        totalTime += (System.nanoTime() - t1) - (gct2 - gct1)

         t1 = System.nanoTime()
         gct1 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
         var z = pullMin(tinput)
         gct2 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
        ptotalTime += (System.nanoTime() - t1) - (gct2 - gct1)
      }
      println(s"$i kthmin ${totalTime/1000000000.0} pullmin ${ptotalTime/1000000000.0}")
    }
  }
}

package rtq

import leon._
import mem._
import higherorder._
import lang._
import annotation._
import collection._
import instrumentation._
import invariant._

/**
 * Requires unrollfactor=2
 */
object RealTimeQueue {

  sealed abstract class Stream[T] {
    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case c@SCons(_, _) => 1 + (c.tail*).size
      }
    } 

    lazy val tail: Stream[T] = {
      this match {
        case SCons(x, tailFun) => tailFun()
      }
    }
  }
  // wellfoundedness prop: (tailFun*).rank < this.rank && \forall x. rank >= 0 && tailFun*.satisfies prop
  private case class SCons[T](x: T, tailFun: () => Stream[T]) extends Stream[T]
  private case class SNil[T]() extends Stream[T]

  @invisibleBody
  @invstate // says that the function doesn't change state
  def rotate[T](f: Stream[T], r: List[T], a: Stream[T]): Stream[T] = {
    (f, r) match {
      case (SNil(), Cons(y, _)) => //in this case 'y' is the only element in 'r'
        SCons[T](y, lift(a)) //  rank: a.rank + 1
      case (c@SCons(x, _), Cons(y, r1)) =>
        val newa = SCons[T](y, lift(a)) // rank : a.rank + 1
        val ftail = c.tail
        val rot = () => rotate(ftail, r1, newa)
        SCons[T](x, rot) // @ rank == f.rank + r.rank + a.rank
    }
  } 

  case class Queue[T](f: Stream[T], r: List[T], s: Stream[T]) 

  @inline
  def createQ[T](f: Stream[T], r: List[T], s: Stream[T]) = {
    s match {
      case c@SCons(_, _) => Queue(f, r, c.tail) // force the schedule once
      case SNil() =>
        val rotres = rotate(f, r, SNil[T]())
        Queue(rotres, Nil(), rotres)
    }
  }

  def empty[T] = {
    val a: Stream[T] = SNil()
    Queue(a, Nil(), a)
  }

  def head[T](q: Queue[T]): T = {
    q.f match {
      case SCons(x, _) => x
    }
  }

  def enqueue[T](x: T, q: Queue[T]): Queue[T] = {
    createQ(q.f, Cons(x, q.r), q.s)
  } 

  def dequeue[T](q: Queue[T]): Queue[T] = {
    q.f match {
      case c@SCons(x, _) =>
        createQ(c.tail, q.r, q.s)
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

    val nooftimes = (1 to 10000000)
    val length = ((1 << 20) - 1)
    var totalTime = 0L
    var rtq = empty[Boolean]
    for (i <- 0 until length) {
      rtq = enqueue[Boolean](false, rtq)
    }

    nooftimes.foreach { _ =>
      var t1 = System.nanoTime()
      var gct1 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
      val r = enqueue[Boolean](false, rtq)
      var gct2 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
      totalTime += (System.nanoTime() - t1) - (gct2 - gct1)
    }
    println(s"${totalTime/1000000000.0} s")
  }
}

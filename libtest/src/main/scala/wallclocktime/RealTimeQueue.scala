package rtqwc

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
    @inline
    def isEmpty: Boolean = this == SNil[T]()
    @inline
    def isCons: Boolean = !isEmpty

    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case c@SCons(_, _) => 1 + (c.tail*).size
      }
    } 

    lazy val tail: Stream[T] = {
      require(isCons)
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
  /**
   * Returns the first element of the stream whose tail is not evaluated.
   */
  // @invisibleBody
  def firstUnevaluated[T](l: Stream[T]): Stream[T] = {
    l match {
      case c @ SCons(_, _) =>
        if (c.tail.cached)
          firstUnevaluated(c.tail*)
        else l
      case _           => l
    }
  }

  case class Queue[T](f: Stream[T], r: List[T], s: Stream[T]) {
    @inline
    def isEmpty = f.isEmpty

    //@inline
    def valid = {
      (firstUnevaluated(f) == firstUnevaluated(s)) &&
        s.size == f.size - r.size //invariant: |s| = |f| - |r|
    }
  }

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
    require(!q.isEmpty && q.valid)
    q.f match {
      case SCons(x, _) => x
    }
  } //ensuring (res => res.valid && time <= ?)

  def enqueue[T](x: T, q: Queue[T]): Queue[T] = {
    createQ(q.f, Cons(x, q.r), q.s)
  } 

  def dequeue[T](q: Queue[T]): Queue[T] = {
    q.f match {
      case c@SCons(x, _) =>
        createQ(c.tail, q.r, q.s)
    }
  } 
  
  def main(args: Array[String]) {
    import scala.util.Random
    import scala.math.BigInt
    import stats._
    import scala.util.Random
    import java.lang.management._
    import scala.collection.JavaConversions._
    import java.lang.management._

    val rand = Random

    val nooftimes = (1 to 100000000)
    val points = (5 to 15)
    val length = points.map(x => ((1 << x) - 1))    

    length.foreach { i =>
      var totalTime = 0L
      var ptotalTime = 0L
      var rtq = empty[BigInt]
      for (i <- 0 until i) {
        rtq = enqueue[BigInt](BigInt(0), rtq)
      }

      nooftimes.foreach { _ =>
        var t1 = System.nanoTime()
        var gct1 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
        var r = enqueue(BigInt(0), rtq)
        var gct2 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
        totalTime += (System.nanoTime() - t1) - (gct2 - gct1)
      }
      println(s"$i rtqenqueue ${totalTime/1000000000.0}")
    }

    length.foreach { i =>
      var totalTime = 0L
      var ptotalTime = 0L
      var rtq = empty[BigInt]
      for (i <- 0 until i) {
        rtq = enqueue[BigInt](BigInt(0), rtq)
      }

      nooftimes.foreach { _ =>
        var t1 = System.nanoTime()
        var gct1 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
        var r = dequeue(rtq)
        var gct2 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
        totalTime += (System.nanoTime() - t1) - (gct2 - gct1)
      }
      println(s"$i rtqenqueue ${totalTime/1000000000.0}")
    }
  }
}

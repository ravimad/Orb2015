package lbumswc

import leon._
// import lang._
import annotation._
import instrumentation._
import invariant._
import mem._
import higherorder._
import stats._
import leon.runtimeDriver._
import scala.math._
// import scala.collection.immutable._
/**
 * Computing the kthe min using a version of merge sort that operates bottom-up.
 * This allows accessing the first element in the sorted list in O(n) time,
 * and kth element in O(kn) time.
 * Needs unrollfactor = 3
 */
object BottomUpMergeSortPrecise {

  @inline
  def max(x:BigInt, y:BigInt) = if (x >= y) x else y
  
  sealed abstract class List[T] {
    // size is used in the specs
    def size: BigInt = (this match {
      case Nil() => BigInt(0)
      case Cons(h, t) => 1 + t.size
    }) 
  }
  case class Cons[T](x: T, tail: List[T]) extends List[T]
  case class Nil[T]() extends List[T]
  
  private sealed abstract class LList {
    def size: BigInt = {
      this match {
        case SCons(_, t) => 1 + t.size
        case _            => BigInt(0)
      }
    } ensuring (_ >= 0)
  }
  private case class SCons(x: BigInt, tailFun: Stream) extends LList
  private case class SNil() extends LList
  private case class Stream(lfun: () => LList) {
    @inline
    def size = (list*).size
    lazy val list: LList = lfun()
  }

  @inline
  private val nilStream: Stream = Stream(() => SNil())

  /**
   *
   * this method is a functional implementation of buildheap in linear time.
   */
  @invisibleBody
  private def constructMergeTree(l: List[BigInt], from: BigInt, to: BigInt): (LList, List[BigInt]) = {
    l match {
      case Nil()           => (SNil(), Nil[BigInt]()) // this case is unreachable
      case Cons(x, tail)  =>
        if(from == to) (SCons(x, nilStream), tail)
        else {
          val mid = (from + to) / 2
          val (lside, midlist) = constructMergeTree(l, from, mid)
          val (rside, rest) = constructMergeTree(midlist, mid + 1, to)
          (merge(lside, rside), rest)
        }
    }
  }

  @invisibleBody
  private def merge(a: LList, b: LList): LList = {
    b match {
      case SNil() => a
      case SCons(x, xs) =>
        a match {
          case SNil() => b
          case SCons(y, ys) =>
            if (y < x)
              SCons(y, Stream(() => mergeSusp(b, ys))) // here, the order of arguments is changed, the sort is not a stable sort
            else
              SCons(x, Stream(() => mergeSusp(a, xs)))
        }
    }
  } 

  /**
   *  A function that merges two sorted streams of integers.
   *  Note: the sorted stream of integers may by recursively constructed using merge.
   *  Takes time linear in the size of the streams (non-trivial to prove due to cascading of lazy calls)
   */
  @invisibleBody
  private def mergeSusp(a: LList, b: Stream): LList = {
    merge(a, b.list)
  } 

  /**
   * Takes list of integers and returns a sorted stream of integers.
   * Takes time linear in the size of the  input since it sorts lazily.
   */
  @invisibleBody
  private def mergeSort(l: List[BigInt]): LList = {
    l match {
      case Nil() => SNil()
      case _ => constructMergeTree(l, 0, l.size- 1)._1
    }
  } 

  private def kthMinRec(l: LList, k: BigInt): BigInt = { // note: making this invisibleBody breaks lemms instantiation, why ?
    l match {
      case SCons(x, xs) =>
        if (k == 0) x
        else
          kthMinRec(xs.list, k - 1)
      case SNil() => BigInt(0)
    }
  } ensuring (_ => time <= ?) //  time <= 36 * (k * l.height) + 17
  //TODO Add the ? * (l.height) term if the numbers do not match the runtime estimate

  /**
   * A function that accesses the kth element of a list using lazy sorting.
   */
  def kthMin(l: List[BigInt], k: BigInt): BigInt = {
    kthMinRec(mergeSort(l), k)
  } ensuring(_ => time <= ?) // 36 * (k * log(l.size - 1)) + 56 * l.size + 22



  def main(args: Array[String]): Unit = {
    import scala.util.Random
    import scala.math.BigInt
    import stats._
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
      // val input = sort(tinput) match {
      //   case SCons(_, t) => t
      //   case SNil() => Stream(()=>SNil())
      // }
      nooftimes.foreach { _ =>
        var t1 = System.nanoTime()
        // val x = sort(tinput) match {
        //   case SCons(_, t) => t
        //   case SNil() => Stream(()=>SNil())
        // }
        var gct1 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
        var r = kthMin(tinput, 10)
        var gct2 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
        totalTime += (System.nanoTime() - t1) - (gct2 - gct1)

        //  t1 = System.nanoTime()
        //  gct1 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
        //  var z = pullMin(tinput)
        //  gct2 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
        // ptotalTime += (System.nanoTime() - t1) - (gct2 - gct1)
      }
      println(s"$i kthmin ${totalTime/1000000000.0}")
    }
  }
}

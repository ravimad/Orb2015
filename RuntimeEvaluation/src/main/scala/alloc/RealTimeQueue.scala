package allocAnalysis

import leon.collection._
import leon._
import leon.mem._
import leon.higherorder._
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.instrumentation._
import leon.invariant._
import leon.runtimeDriver._
import scala.collection.mutable.{ListBuffer => scalaList}

object RealTimeQueue {

  abstract class Stream2[T]

  case class SCons1[T](x345 : T, tailFun19 : () => (Stream2[T], BigInt)) extends Stream2[T]
  def empty[T] = {
    val a: Stream2[T] = SNil1()
    Queue2(a, Nil(), a)
  }

  case class SNil1[T]() extends Stream2[T]

  case class Queue2[T](f160 : Stream2[T], r196 : List[T], s106 : Stream2[T])

  @invisibleBody
  @invstate
  def rotatealloc[T](f : Stream2[T], r : List[T], a : Stream2[T]): (Stream2[T], BigInt) = {
    val bd3 = (f, r) match {
      case (SNil1(), Cons(y, _)) =>
        (SCons1[T](y, () => (a, BigInt(0))), BigInt(2))
      case (c19 @ SCons1(x, _), Cons(y, r1)) =>
        val ir15 = SCons1[T](y, () => (a, BigInt(0)))
        val lr = lookup[Stream2[T]](List(5271, c19))
        val ir1 = if (lr._1) {
          (lr._2, BigInt(0))
        } else {
          val e21 = Stream.tailalloc[T](c19)
          (update[Stream2[T]](List(5271, c19), e21._1), BigInt(1) + e21._2)
        }
        (SCons1[T](x, () => {
          val e25 = rotatealloc[T](ir1._1, r1, ir15)
          (e25._1, e25._2)
        }), BigInt(4) + ir1._2)
    }
    (bd3._1, bd3._2)
  }

  def enqueuealloc[T](x : T, q : Queue2[T]): (Queue2[T], BigInt) = {
    val ir9 = q.f160
    val ir11 = Cons[T](x, q.r196)
    val r208 = q.s106 match {
      case c20 @ SCons1(_, _) =>
        val lr1 = lookup[Stream2[T]](List(5271, c20))
        val e37 = if (lr1._1) {
          (lr1._2, BigInt(0))
        } else {
          val e36 = Stream.tailalloc[T](c20)
          (update[Stream2[T]](List(5271, c20), e36._1), BigInt(1) + e36._2)
        }
        (Queue2[T](ir9, ir11, e37._1), BigInt(1) + e37._2)
      case SNil1() =>
        val e41 = rotatealloc[T](ir9, ir11, SNil1[T]())
        val e69 = e41._1
        (Queue2[T](e69, List[T](), e69), BigInt(3) + e41._2)
    }
    (r208._1, BigInt(1) + r208._2)
  }

  def dequeuealloc[T](q : Queue2[T]): (Queue2[T], BigInt) = {
    val bd5 = {
      val c22 @ SCons1(x, _) = q.f160
      val lr2 = lookup[Stream2[T]](List(5271, c22))
      val ir6 = if (lr2._1) {
        (lr2._2, BigInt(0))
      } else {
        val e47 = Stream.tailalloc[T](c22)
        (update[Stream2[T]](List(5271, c22), e47._1), BigInt(1) + e47._2)
      }
      val ir17 = q.r196
      val r225 = q.s106 match {
        case c23 @ SCons1(_, _) =>
          val lr3 = lookup[Stream2[T]](List(5271, c23))
          val e54 = if (lr3._1) {
            (lr3._2, BigInt(0))
          } else {
            val e53 = Stream.tailalloc[T](c23)
            (update[Stream2[T]](List(5271, c23), e53._1), BigInt(1) + e53._2)
          }
          (Queue2[T](ir6._1, ir17, e54._1), BigInt(1) + e54._2)
        case SNil1() =>
          val e58 = rotatealloc[T](ir6._1, ir17, SNil1[T]())
          (Queue2[T](e58._1, List[T](), e58._1), BigInt(3) + e58._2)
      }
      (r225._1, r225._2 + ir6._2)
    }
    (bd5._1, bd5._2)
  }

  // def main(args: Array[String]): Unit = {
  //   import scala.util.Random
  //   val rand = Random

  //   val points = (0 to 18)
  //   val size = points.map(x => BigInt((1 << x) - 1)).to[scalaList]
  //   val size2 = points.map(x => ((1 << x) - 1)).toList

  //   var ops = List[BigInt]()
  //   var orb = List[BigInt]()
  //   size2.foreach { length =>
  //     var rtq = empty[BigInt]
  //     for (i <- 0 until length) {
  //       rtq = enqueuealloc[BigInt](BigInt(0), rtq)._1
  //     }
  //     ops :+= {7}
  //     orb :+= {8}
  //   }
  //   dumpdata(size2, ops, orb, "rtqenqueue", "orb")
  //   minresults(ops, scalaList(8), List("constant"), List(), size, "rtqenqueue")

  //   // ops = List[() => BigInt]()
  //   // orb = List[() => BigInt]()
  //   // size2.foreach { length =>
  //   //   var rtq = empty[BigInt]
  //   //   for (i <- 0 until length) {
  //   //     rtq = enqueuealloc[BigInt](BigInt(0), rtq)._1
  //   //   }
  //   //   ops :+= {6}
  //   //   orb :+= {7}
  //   // }
  //   // dumpdata(size2, ops, orb, "rtqdequeue", "orb")
  //   // minresults(ops, scalaList(7), List("constant"), List(), size, "rtqdequeue")
  // }

  /**
   * Benchmark specific parameters
   */
  abstract class RunContext {
    def coeffs: scalaList[BigInt] //from lower to higher-order terms
    def coeffNames = List("constant") // names of the coefficients
    val termsSize = 0 // number of terms (i.e monomials) in the template
    def getTermsForPoint(i: BigInt): scalaList[BigInt] = scalaList()
    def inputFromPoint(i: Int) = {
      val len = ((1 << i) - 1)
      var rtq = empty[BigInt]
      for (i <- 0 until len) {
        rtq = enqueuealloc[BigInt](BigInt(0), rtq)._1
      }
      rtq
    }
    val dirname = "alloc/RealTimeQueue"
    val filePrefix: String
    val points = (1 to 20)
    val concreteInstFun: Queue2[BigInt] => BigInt

  }
  object EnqueueContext extends RunContext {
    override def coeffs = scalaList[BigInt](8)
    override val filePrefix = "rtq-enqueue" // the abbrevation used in the paper
    override val concreteInstFun = (rtq: Queue2[BigInt]) => enqueuealloc[BigInt](BigInt(0), rtq)._2
  }

  object DequeueContext extends RunContext {
    override def coeffs = scalaList[BigInt](7)
    override val filePrefix = "rtq-dequeue" // the abbrevation used in the paper
    override val concreteInstFun = (rtq: Queue2[BigInt]) => dequeuealloc[BigInt](rtq)._2
  }
  val ctxts: scalaList[RunContext] = scalaList(EnqueueContext, DequeueContext)
  /**
   * Benchmark agnostic helper functions
   */
  def benchmark(ctx: RunContext) {
    import ctx._
    def template(coeffs: scalaList[BigInt], terms: scalaList[BigInt]) = {
      coeffs.head + (coeffs.tail zip terms).map { case (coeff, term) => coeff * term }.sum
    }
    def boundForInput(terms: scalaList[BigInt]): BigInt = template(coeffs, terms)
    def computeTemplate(coeffs: scalaList[BigInt], terms: scalaList[BigInt]): BigInt = {
      template(coeffs, terms)
    }
    val size = points.map(x => BigInt(x)).to[scalaList]
    val size2 = points.map(x => (x)).toList
    var ops = scalaList[BigInt]()
    var orb = scalaList[BigInt]()
    var termsforInp = (0 until termsSize).map(_ => scalaList[BigInt]()).toList
    val concreteOps = concreteInstFun
    points.foreach { i =>
      println("Processing input: " + i)
      leon.mem.clearMemo()
      val input = inputFromPoint(i)
      ops += concreteOps(input)
      // compute the static bound
      val terms = getTermsForPoint(i)
      orb += boundForInput(terms)
      terms.zipWithIndex.foreach {
        case (term, i) => termsforInp(i) += term
      }
    }
    val minlist = mindirresults(ops, coeffs, coeffNames, termsforInp, size, filePrefix, dirname)
    val minresults = minlist.map { l =>
      points.map { i =>
        computeTemplate(l, getTermsForPoint(i))
      }.to[scalaList]
    }
    dumpdirdata(size2, ops, orb, filePrefix, "dynamic", dirname)
    var i = 0
    minlist.foreach { l =>
      dumpdirdata(size2, minresults(i), orb, filePrefix, s"pareto$i", dirname)
      i = i + 1
    }
  }

  def main(args: Array[String]): Unit = {
    ctxts.foreach(benchmark)
  }

  object Stream {
  def tailalloc[T](thiss : RealTimeQueue.Stream2[T]): (RealTimeQueue.Stream2[T], BigInt) = {
    val bd6 = {
      val RealTimeQueue.SCons1(x, tailFun33) = thiss
      val e63 = tailFun33()
      (e63._1, e63._2)
    }
    (bd6._1, bd6._2)
  }
}

}

object Queue {

}

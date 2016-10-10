package stepsAnalysis

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
import scala.collection.mutable.{ ListBuffer => scalaList }

object RealTimeQueue {

  abstract class Stream2[T]

  case class SCons1[T](x345: T, tailFun19: () => (Stream2[T], BigInt)) extends Stream2[T]
  def empty[T] = {
    val a: Stream2[T] = SNil1()
    Queue2(a, Nil(), a)
  }

  case class SNil1[T]() extends Stream2[T]

  case class Queue2[T](f161: Stream2[T], r196: List[T], s106: Stream2[T])

  @invisibleBody
  @invstate
  def rotatetime[T](f: Stream2[T], r: List[T], a: Stream2[T]): (Stream2[T], BigInt) = {
    val bd4 = (f, r) match {
      case (SNil1(), Cons(y, _)) =>
        (SCons1[T](y, () => (a, BigInt(0))), BigInt(10))
      case (c18 @ SCons1(x, _), Cons(y, r1)) =>
        val ir17 = SCons1[T](y, () => (a, BigInt(0)))
        val lr = lookup[Stream2[T]](List(5273, c18))
        val ir1 = if (lr._1) {
          (lr._2, BigInt(1))
        } else {
          val e23 = Stream.tailtime[T](c18)
          (update[Stream2[T]](List(5273, c18), e23._1), BigInt(3) + e23._2)
        }
        (SCons1[T](x, () => {
          val e27 = rotatetime[T](ir1._1, r1, ir17)
          (e27._1, BigInt(1) + e27._2)
        }), BigInt(19) + ir1._2)
    }
    (bd4._1, bd4._2)
  }

  def enqueuetime[T](x: T, q: Queue2[T]): (Queue2[T], BigInt) = {
    val ir11 = q.f161
    val ir13 = Cons[T](x, q.r196)
    val r214 = q.s106 match {
      case c20 @ SCons1(_, _) =>
        val lr1 = lookup[Stream2[T]](List(5273, c20))
        val e39 = if (lr1._1) {
          (lr1._2, BigInt(1))
        } else {
          val e38 = Stream.tailtime[T](c20)
          (update[Stream2[T]](List(5273, c20), e38._1), BigInt(3) + e38._2)
        }
        (Queue2[T](ir11, ir13, e39._1), BigInt(4) + e39._2)
      case SNil1() =>
        val e43 = rotatetime[T](ir11, ir13, SNil1[T]())
        val e77 = e43._1
        (Queue2[T](e77, List[T](), e77), BigInt(8) + e43._2)
    }
    (r214._1, BigInt(3) + r214._2)
  }

  def dequeuetime[T](q: Queue2[T]): (Queue2[T], BigInt) = {
    val bd6 = {
      val c23 @ SCons1(x, _) = q.f161
      val lr2 = lookup[Stream2[T]](List(5273, c23))
      val ir6 = if (lr2._1) {
        (lr2._2, BigInt(1))
      } else {
        val e49 = Stream.tailtime[T](c23)
        (update[Stream2[T]](List(5273, c23), e49._1), BigInt(3) + e49._2)
      }
      val ir9 = q.r196
      val r227 = q.s106 match {
        case c24 @ SCons1(_, _) =>
          val lr3 = lookup[Stream2[T]](List(5273, c24))
          val e56 = if (lr3._1) {
            (lr3._2, BigInt(1))
          } else {
            val e55 = Stream.tailtime[T](c24)
            (update[Stream2[T]](List(5273, c24), e55._1), BigInt(3) + e55._2)
          }
          (Queue2[T](ir6._1, ir9, e56._1), BigInt(4) + e56._2)
        case SNil1() =>
          val e60 = rotatetime[T](ir6._1, ir9, SNil1[T]())
          (Queue2[T](e60._1, List[T](), e60._1), BigInt(8) + e60._2)
      }
      (r227._1, (BigInt(5) + r227._2) + ir6._2)
    }
    (bd6._1, bd6._2)
  }

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
        rtq = enqueuetime[BigInt](BigInt(0), rtq)._1
      }
      rtq
    }
    val dirname = "steps/RealTimeQueue"
    val filePrefix: String
    val points = (5 to 15)
    val concreteInstFun: Queue2[BigInt] => BigInt

  }
  object EnqueueContext extends RunContext {
    override def coeffs = scalaList[BigInt](37)
    override val filePrefix = "rtq-enqueue" // the abbrevation used in the paper  
    override val concreteInstFun = (rtq: Queue2[BigInt]) => enqueuetime[BigInt](BigInt(0), rtq)._2
  }

  object DequeueContext extends RunContext {
    override def coeffs = scalaList[BigInt](40)
    override val filePrefix = "rtq-dequeue" // the abbrevation used in the paper  
    override val concreteInstFun = (rtq: Queue2[BigInt]) => dequeuetime[BigInt](rtq)._2
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
    def tailtime[T](thiss: RealTimeQueue.Stream2[T]): (RealTimeQueue.Stream2[T], BigInt) = {
      val bd = {
        val RealTimeQueue.SCons1(x, tailFun21) = thiss
        val e15 = tailFun21()
        (e15._1, BigInt(5) + e15._2)
      }
      (bd._1, bd._2)
    }
  }
}

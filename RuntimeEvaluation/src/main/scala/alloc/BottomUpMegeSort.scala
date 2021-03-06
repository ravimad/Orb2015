package allocAnalysis

import leon.collection._
import leon._
// import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.mem._
import leon.higherorder._
import leon.stats._
import leon.runtimeDriver._
import scala.math._
import scala.collection.mutable.{ListBuffer => scalaList}

object BottomUpMergeSort {

  def mylog(x: BigInt) : BigInt = {
    if(x < 0) BigInt(1)
    else if(x == 0) BigInt(2)
    else
      1 + mylog(x/2)
  }

  
  abstract class LList2
  
  
  case class SCons1(x322 : BigInt, tailFun1 : Stream2) extends LList2
  
  
  case class SNil1() extends LList2
  
  
  case class Stream2(lfun1 : () => (LList2, BigInt))
  
  @invisibleBody
  def constructMergeTreealloc(l : List[BigInt], from : BigInt, to : BigInt): ((LList2, List[BigInt]), BigInt) = {
    val bd2 = l match {
      case Nil() =>
        ((SNil1(), Nil[BigInt]()), BigInt(2))
      case Cons(x, tail) =>
        val mc5 = if (from == to) {
          ((SCons1(x, Stream2(() => (SNil1(), BigInt(1)))), tail), BigInt(3))
        } else {
          val ir7 = (from + to) / BigInt(2)
          val e37 = constructMergeTreealloc(l, from, ir7)
          val ir1 = {
            val (lside, midlist) = e37._1
            ((lside, midlist), e37._2)
          }
          val ir9 = ir1._1
          val e47 = constructMergeTreealloc(ir9._2, BigInt(1) + ir7, to)
          val ir4 = {
            val (rside, rest) = e47._1
            ((rside, rest), e47._2)
          }
          val ir15 = ir4._1
          val e54 = mergealloc(ir9._1, ir15._1)
          ((e54._1, ir15._2), (e54._2 + ir4._2) + ir1._2)
        }
        (mc5._1, mc5._2)
    }
    (bd2._1, bd2._2)
  }
  
  @invisibleBody
  def mergealloc(a : LList2, b : LList2): (LList2, BigInt) = {
    val bd5 = b match {
      case SNil1() =>
        (a, BigInt(0))
      case SCons1(x, xs34) =>
        val mc9 = a match {
          case SNil1() =>
            (b, BigInt(0))
          case SCons1(y, ys2) =>
            val mc8 = if (y < x) {
              (SCons1(y, Stream2(() => {
                val e62 = mergeSuspalloc(b, ys2)
                (e62._1, e62._2)
              })), BigInt(3))
            } else {
              (SCons1(x, Stream2(() => {
                val e68 = mergeSuspalloc(a, xs34)
                (e68._1, e68._2)
              })), BigInt(3))
            }
            (mc8._1, mc8._2)
        }
        (mc9._1, mc9._2)
    }
    (bd5._1, bd5._2)
  }
  
  @invisibleBody
  def mergeSuspalloc(a : LList2, b : Stream2): (LList2, BigInt) = {
    val lr = lookup[LList2](List(4971, b))
    val e79 = if (lr._1) {
      (lr._2, BigInt(0))
    } else {
      val e78 = Stream.listalloc(b)
      (update[LList2](List(4971, b), e78._1), BigInt(1) + e78._2)
    }
    val e80 = mergealloc(a, e79._1)
    (e80._1, e80._2 + e79._2)
  }
  
  @invisibleBody
  def mergeSortalloc(l : List[BigInt]): (LList2, BigInt) = {
    val bd = l match {
      case Nil() =>
        (SNil1(), BigInt(1))
      case _ =>
        val e21 = constructMergeTreealloc(l, BigInt(0), (l.size) - BigInt(1))
        (e21._1._1, e21._2)
    }
    (bd._1, bd._2)
  }
  
  def kthMinRecalloc(l : LList2, k : BigInt): (BigInt, BigInt) = {
    val bd9 = l match {
      case SCons1(x, xs35) =>
        val mc10 = if (k == BigInt(0)) {
          (x, BigInt(0))
        } else {
          val lr1 = lookup[LList2](List(4971, xs35))
          val e88 = if (lr1._1) {
            (lr1._2, BigInt(0))
          } else {
            val e87 = Stream.listalloc(xs35)
            (update[LList2](List(4971, xs35), e87._1), BigInt(1) + e87._2)
          }
          val e92 = kthMinRecalloc(e88._1, k - BigInt(1))
          (e92._1, e92._2 + e88._2)
        }
        (mc10._1, mc10._2)
      case SNil1() =>
        (BigInt(0), BigInt(0))
    }
    (bd9._1, bd9._2)
  }
  
  def kthMinalloc(l : List[BigInt], k : BigInt): (BigInt, BigInt) = {
    val e82 = mergeSortalloc(l)
    val e85 = kthMinRecalloc(e82._1, k)
    (e85._1, e85._2 + e82._2)
  }
  
  // def main(args: Array[String]): Unit = {
  //   import scala.util.Random
  //   val rand = Random

  //   val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
  //   val size = points.map(x => (x)).toList
    
  //   var ops = List[BigInt]()
  //   var orb = List[BigInt]()
  //   var valueForklogn = scalaList[BigInt]()
  //   var valueForn = scalaList[BigInt]()

  //   points.foreach { i =>
  //     val input = {
  //       (1 to i).foldLeft[List[BigInt]](Nil()) { (f, n) =>
  //         Cons(n, f)  
  //       }
  //     }
  //     ops :+= {-1 * 86 + 6*3*mylog(i - 1) + 6*BigInt(i)}
  //     valueForklogn :+= {3*mylog(i - 1)}
  //     valueForn :+= {BigInt(i)}
  //     orb :+= {3 + 6*3*mylog(i - 1) + 6*BigInt(i)}
  //   }
  //   // minresults(ops, scalaList(3, 6, 6), List("constant", "3*log(n - 1)", "n"), List(valueForklogn, valueForn), size, "lbumskthMin")
  //   dumpdata(size, ops, orb, "lbums", "orb")
  // }
//  def coeffs = scalaList[BigInt](3, 6, 6) //from lower to higher-order terms
//  def coeffNames = List("constant", "n", "3*log (n-1)") // names of the coefficients
//  val termsSize = 2 // number of terms (i.e monomials) in the template
//  def getTermsForPoint(length: BigInt) = scalaList(length, 3 * mylog(length - 1))
//  def inputFromPoint(length: Int) = {    
//    val input = {
//      (1 to length).foldLeft[List[BigInt]](Nil()) { (f, n) =>
//        Cons(n, f)
//      }
//    }
//    input
//  }
//  val dirname = 
//  val filePrefix = "msort" // the abbrevation used in the paper
//  val points = (1000 to 10000 by 1000)
//  val concreteInstFun = (input: List[BigInt]) => kthMinalloc(input, 3)._2
/**
   * Benchmark specific parameters
   */
  object RunContext {
    def coeffs = scalaList[BigInt](3, 6, 6) //from lower to higher-order terms
    def coeffNames = List("constant", "n", "k*log (n-1)") // names of the coefficients
    val termsSize = 2 // number of terms (i.e monomials) in the template
    def getTermsForPoint(length: BigInt, k: BigInt) = scalaList(length, k * mylog(length - 1))
    def inputFromPoint(length: Int) = {
      val input = {
        (1 to length).foldLeft[List[BigInt]](Nil()) { (f, n) =>
          Cons(n, f)
        }
      }
      input
    }
    val dirname = "alloc/BottomUpMergeSort"
    val filePrefix = "msort" // the abbrevation used in the paper
    val points = (1 to 100).flatMap(k => (1000 to 10000 by 1000).map(n => (n, k)))
    val concreteInstFun = (input: List[BigInt], k: BigInt) => kthMinalloc(input, k)._2
  }  

  /**
   * Benchmark agnostic helper functions
   */
  def benchmark {
    import RunContext._
    def template(coeffs: scalaList[BigInt], terms: scalaList[BigInt]) = {
      coeffs.head + (coeffs.tail zip terms).map { case (coeff, term) => coeff * term }.sum
    }
    def boundForInput(terms: scalaList[BigInt]): BigInt = template(coeffs, terms)
    def computeTemplate(coeffs: scalaList[BigInt], terms: scalaList[BigInt]): BigInt = {
      template(coeffs, terms)
    }
    val size = points.map(x => BigInt(x._1)).to[scalaList] // ignore k here
    val size2 = points.map(x => (x._1)).toList // ignore k here
    var ops = scalaList[BigInt]()
    var orb = scalaList[BigInt]()
    var termsforInp = (0 until termsSize).map(_ => scalaList[BigInt]()).toList
    val concreteOps = concreteInstFun
    points.foreach { case (i, k) =>
      println("Processing input: " + (i, k))
      leon.mem.clearMemo()
      val input = inputFromPoint(i)
      ops += concreteOps(input, k)
      // compute the static bound
      val terms = getTermsForPoint(i, k)
      orb += boundForInput(terms)
      terms.zipWithIndex.foreach {
        case (term, i) => termsforInp(i) += term
      }
    }
    val minlist = mindirresults(ops, coeffs, coeffNames, termsforInp, size, filePrefix, dirname)
    val minresults = minlist.map { l =>
      points.map { case (i, k) =>
        computeTemplate(l, getTermsForPoint(i, k))
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
    benchmark
  }

  object Stream {
  def listalloc(thiss : BottomUpMergeSort.Stream2): (BottomUpMergeSort.LList2, BigInt) = {
    val e75 = thiss.lfun1()
    (e75._1, e75._2)
  }
}
}



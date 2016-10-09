package allocAnalysis

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.runtimeDriver._
import scala.collection.mutable.{ListBuffer => scalaList}

object Knapscak {
  abstract class IList
  
  case class Cons(x : (BigInt, BigInt), tail : IList) extends IList
  
  case class Nil() extends IList
  
  @invstate
  def maxValuealloc(items : IList, w : BigInt, currList : IList): (BigInt, BigInt) = {
    val bd = currList match {
      case Cons((wi, vi), tail) =>
        val e17 = maxValuealloc(items, w, tail)
        val e93 = e17._1
        val r159 = if (wi <= w && wi > BigInt(0)) {
          val e99 = w - wi
          val lr = lookup[BigInt](List(4870, e99, items))
          val e24 = if (lr._1) {
            (lr._2, BigInt(0))
          } else {
            val e23 = knapSackalloc(e99, items)
            (update[BigInt](List(4870, e99, items), e23._1), BigInt(1) + e23._2)
          }
          val ir1 = (vi + e24._1, e24._2)
          val e25 = (ir1._1, BigInt(0))
          val r158 = if (ir1._1 >= e93) {
            (ir1._1, e25._2)
          } else {
            (e93, e25._2)
          }
          (r158._1, r158._2 + e24._2)
        } else {
          (e93, BigInt(0))
        }
        (r159._1, r159._2 + e17._2)
      case Nil() =>
        (BigInt(0), BigInt(0))
    }
    (bd._1, bd._2)
  }
  
  @memoize
  def knapSackalloc(w : BigInt, items : IList): (BigInt, BigInt) = {
    val bd2 = if (w == BigInt(0)) {
      (BigInt(0), BigInt(0))
    } else {
      val e39 = maxValuealloc(items, w, items)
      (e39._1, e39._2)
    }
    (bd2._1, bd2._2)
  }
  
  @invisibleBody
  def invokealloc(i : BigInt, items : IList): (BigInt, BigInt) = {
    val lr1 = lookup[BigInt](List(4870, i, items))
    val bd1 = if (lr1._1) {
      (lr1._2, BigInt(0))
    } else {
      val e35 = knapSackalloc(i, items)
      (update[BigInt](List(4870, i, items), e35._1), BigInt(1) + e35._2)
    }
    (bd1._1, bd1._2)
  }
  
  def bottomupalloc(w : BigInt, items : IList): (IList, BigInt) = {
    val bd4 = if (w == BigInt(0)) {
      val e48 = invokealloc(w, items)
      (Cons((w, e48._1), Nil()), BigInt(2) + e48._2)
    } else {
      val e56 = bottomupalloc(w - BigInt(1), items)
      val e60 = invokealloc(w, items)
      (Cons((w, e60._1), e56._1), (BigInt(1) + e60._2) + e56._2)
    }
    (bd4._1, bd4._2)
  }
  
  def knapSackSolalloc(w : BigInt, items : IList): (IList, BigInt) = {
    val e44 = bottomupalloc(w, items)
    (e44._1, e44._2)
  }

  // def main(args: Array[String]): Unit = {
  //   import scala.util.Random
  //   val rand = Random

  //   val points = (10 to 200 by 10) ++ (100 to 1000 by 50) //++ (1000 to 10000 by 1000)
  //   val size = points.map(x => (x)).toList
  //   val size2 = points.map(x => BigInt(x)).to[scalaList]

  //   var ops = List[BigInt]()
  //   var orb = List[BigInt]()
  //   var valueForw = scalaList[BigInt]()
  //   var valueForitemsize = scalaList[BigInt]()
  //   var valueForwitemsize = scalaList[BigInt]()
  //   points.foreach { i =>
  //     val w = i
  //     val itemsize = w/4
  //     val input = {
  //       (1 to itemsize).foldLeft[IList](Nil()) { (f, n) =>
  //         Cons((rand.nextInt(itemsize), rand.nextInt(itemsize)), f)  
  //       }
  //     }
  //     ops :+= {
  //         leon.mem.clearMemo()
  //         knapSackSolalloc(w, input)._2
  //     }
  //     orb :+= {2*w + 3}
  //     valueForw :+= {BigInt(w)}
  //     valueForitemsize :+= {BigInt(itemsize)}
  //     valueForwitemsize :+= {BigInt(w*itemsize)}
  //   }
  //   dumpdata(size, ops, orb, "knapsack", "orb")
  //   // minresults(ops, scalaList(3, 2), List("constant", "w"), List(valueForw), size2, "knapsack")
  //}  

import scala.util.Random
  val rand = Random
    /**
   * Benchmark specific parameters
   */
  def coeffs = scalaList[BigInt](3, 2) //from lower to higher-order terms
  def coeffNames = List("constant", "w") // names of the coefficients
  val termsSize = 1 // number of terms (i.e monomials) in the template
  def getTermsForPoint(w: BigInt) = {  
    scalaList(w) 
  }
  def inputFromPoint(i: Int) = {
    val itemsize = i / 4
    // initialize the mutable array
    val input = {
        (1 to itemsize).foldLeft[IList](Nil()) { (f, n) =>
          Cons((rand.nextInt(itemsize), rand.nextInt(itemsize)), f)  
        }
      }
    input
  }
  val dirname = "alloc/Knapsack"
  val filePrefix = "ks"
  val points = (0 to 200 by 10) ++ (100 to 1000 by 50)  
  val concreteInstFun = (w: BigInt, input: IList) => knapSackSolalloc(w, input)._2
  
  /**
   * Benchmark agnostic helper functions
   */
  def template(coeffs: scalaList[BigInt], terms: scalaList[BigInt]) = {
    coeffs.head + (coeffs.tail zip terms).map{ case (coeff, term) => coeff * term }.sum
  }          
  def boundForInput(terms: scalaList[BigInt]): BigInt = template(coeffs, terms)  
  def computeTemplate(coeffs: scalaList[BigInt], terms: scalaList[BigInt]): BigInt = {
    template(coeffs, terms)
  } 

  def main(args: Array[String]): Unit = {    
    val size = points.map(x => BigInt(x)).to[scalaList]
    val size2 = points.map(x => (x)).toList
    var ops = scalaList[BigInt]()
    var orb = scalaList[BigInt]()
    var termsforInp = (0 until termsSize).map( _ =>scalaList[BigInt]()).toList  
    val concreteOps = concreteInstFun
    points.foreach { i =>
      println("Processing input: "+i)
       val input = inputFromPoint(i)            
       ops += concreteOps(i, input)
       // compute the static bound
       val terms = getTermsForPoint(i)
       orb += boundForInput(terms)  
       terms.zipWithIndex.foreach { 
        case (term, i) => termsforInp(i) += term 
      }  
       leon.mem.clearMemo()
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
  
}
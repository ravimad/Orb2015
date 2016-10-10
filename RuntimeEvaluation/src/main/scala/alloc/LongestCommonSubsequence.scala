package allocAnalysis

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.collection._
import leon.runtimeDriver._
import scala.collection.mutable.{ListBuffer => scalaList}

object LongestCommonSubsequence {
  @ignore
  var xstring = Array[BigInt]()
  @ignore
  var ystring = Array[BigInt]()
  
  def lookupalloc(i : BigInt, j : BigInt): ((BigInt, BigInt), BigInt) = (((xstring(i.toInt), ystring(j.toInt)), BigInt(0)) : ((BigInt, BigInt), BigInt))
  
  @invstate
  @memoize
  @invisibleBody
  def lcsalloc(i : BigInt, j : BigInt): (BigInt, BigInt) = {
    val bd = if (i == BigInt(0) || j == BigInt(0)) {
      (BigInt(0), BigInt(0))
    } else {
      val e16 = lookupalloc(i, j)
      val ir = {
        val (xi, yj) = e16._1
        ((xi, yj), e16._2)
      }
      val ir11 = ir._1
      val r160 = if (ir11._1 == ir11._2) {
        val e128 = i - BigInt(1)
        val e130 = j - BigInt(1)
        val lr = lookup[BigInt](List(4881, e128, e130))
        val e28 = if (lr._1) {
          (lr._2, BigInt(0))
        } else {
          val e27 = lcsalloc(e128, e130)
          (update[BigInt](List(4881, e128, e130), e27._1), BigInt(1) + e27._2)
        }
        (BigInt(1) + e28._1, e28._2)
      } else {
        val e134 = i - BigInt(1)
        val lr1 = lookup[BigInt](List(4881, e134, j))
        val ir3 = if (lr1._1) {
          (lr1._2, BigInt(0))
        } else {
          val e34 = lcsalloc(e134, j)
          (update[BigInt](List(4881, e134, j), e34._1), BigInt(1) + e34._2)
        }
        val e138 = j - BigInt(1)
        val lr2 = lookup[BigInt](List(4881, i, e138))
        val ir4 = if (lr2._1) {
          (lr2._2, BigInt(0))
        } else {
          val e39 = lcsalloc(i, e138)
          (update[BigInt](List(4881, i, e138), e39._1), BigInt(1) + e39._2)
        }
        val c10 = (ir3._1 >= ir4._1, BigInt(0))
        val r158 = if (ir3._1 >= ir4._1) {
          (ir3._1, c10._2)
        } else {
          (ir4._1, c10._2)
        }
        (r158._1, (r158._2 + ir4._2) + ir3._2)
      }
      (r160._1, r160._2 + ir._2)
    }
    (bd._1, bd._2)
  }
  
  @invisibleBody
  def invokealloc(i : BigInt, j : BigInt, n : BigInt): (BigInt, BigInt) = {
    val lr3 = lookup[BigInt](List(4881, i, j))
    val bd1 = if (lr3._1) {
      (lr3._2, BigInt(0))
    } else {
      val e52 = lcsalloc(i, j)
      (update[BigInt](List(4881, i, j), e52._1), BigInt(1) + e52._2)
    }
    (bd1._1, bd1._2)
  }
  
  def bottomupalloc(m : BigInt, j : BigInt, n : BigInt): (List[BigInt], BigInt) = {
    val bd2 = if (m == BigInt(0) && j == BigInt(0)) {
      val e56 = invokealloc(m, j, n)
      (List[BigInt](e56._1), BigInt(2) + e56._2)
    } else {
      val el4 = if (j == BigInt(0)) {
        val e64 = bottomupalloc(m - BigInt(1), n, n)
        val e68 = invokealloc(m, j, n)
        (Cons[BigInt](e68._1, e64._1), (BigInt(1) + e68._2) + e64._2)
      } else {
        val e76 = bottomupalloc(m, j - BigInt(1), n)
        val e80 = invokealloc(m, j, n)
        (Cons[BigInt](e80._1, e76._1), (BigInt(1) + e80._2) + e76._2)
      }
      (el4._1, el4._2)
    }
    (bd2._1, bd2._2)
  }
  
  def lcsSolsalloc(m : BigInt, n : BigInt): (List[BigInt], BigInt) = {
    val e94 = bottomupalloc(m, n, n)
    (e94._1, e94._2)
  }

  // def main(args: Array[String]): Unit = {
  //   import scala.util.Random
  //   val rand = Random

  //   val points = (1 to 30 by 1) ++ (100 to 1000 by 50)  //++ (1000 to 10000 by 50)
  //   val size = points.map(x => (x)).toList
    
  //   var ops = List[BigInt]()
  //   var orb = List[BigInt]()
  //   var valuefori2 = scalaList[BigInt]()
  //   var valuefori = scalaList[BigInt]()
    
  //   points.foreach { i =>
  //     val input = i
  //     xstring = Array.fill(i + 1){0}
  //     ystring = Array.fill(i + 1){0}
  //     ops :+= {
  //         leon.mem.clearMemo()
  //         lcsSolsalloc(i, i)._2
  //     }
  //     orb :+= {2*i*i + 2*i + 2*i + 3}
  //     valuefori :+= {BigInt(i)}
  //     valuefori2 :+= {BigInt(i*i)}
      
  //   }
  //   // minresults(ops, scalaList(3, 2, 2, 2), List("constant", "i", "i", "i**2"), List(valuefori, valuefori, valuefori2), size, "lcs")
  //   dumpdata(size, ops, orb, "lcs", "orb")
  // }  
  
    /**
   * Benchmark specific parameters
   */
  def coeffs = scalaList[BigInt](3, 2, 2, 2) //from lower to higher-order terms
  def coeffNames = List("constant", "i", "i", "i**2") // names of the coefficients
  val termsSize = 3 // number of terms (i.e monomials) in the template
  def getTermsForPoint(n: BigInt) = scalaList(n, n, n * n) // terms depend only on n here, but may in general depend on many variables
  def inputFromPoint(i: Int) = {
    // initialize the mutable array
    xstring = Array.fill(i + 1){0}
    ystring = Array.fill(i + 1){0}
    i
  }
  val dirname = "alloc/LCS"
  val filePrefix = "lcs"
  val points = (0 to 30 by 1) ++ (100 to 1000 by 50)  
  val concreteInstFun = (n: BigInt) => lcsSolsalloc(n, n)._2
  
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
       ops += concreteOps(input)
       // compute the static bound
       val terms = getTermsForPoint(i)
       orb += boundForInput(terms)  
       terms.zipWithIndex.foreach { 
        case (term, i) => termsforInp(i) += term 
      }
       //inputfori += //{BigInt(i*i)}
       // We should not clear the cache to measure this
       // orb2 :+= {15*i - 18}     
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

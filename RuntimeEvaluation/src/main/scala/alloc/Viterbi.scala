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

object Viterbi {
  
  def Oalloc(i : BigInt): (BigInt, BigInt) = ((0, 0) : (BigInt, BigInt))
  
  
  def Salloc(i : BigInt): (BigInt, BigInt) = ((0, 0) : (BigInt, BigInt))
  
  
  def Aalloc(i : BigInt, j : BigInt): (BigInt, BigInt) = ((0, 0) : (BigInt, BigInt))
  
  
  def Balloc(i : BigInt, j : BigInt): (BigInt, BigInt) = ((0, 0) : (BigInt, BigInt))
  
  
  def Calloc(i : BigInt): (BigInt, BigInt) = ((0, 0) : (BigInt, BigInt))
  
  
  def Yalloc(i : BigInt): (BigInt, BigInt) = ((0, 0) : (BigInt, BigInt))
  
  @invstate
  def fillEntryalloc(l : BigInt, i : BigInt, j : BigInt, K : BigInt): (BigInt, BigInt) = {
    val e134 = j - BigInt(1)
    val lr = lookup[BigInt](List(4937, l, e134, K))
    val e36 = if (lr._1) {
      (lr._2, BigInt(0))
    } else {
      val e35 = viterbialloc(l, e134, K)
      (update[BigInt](List(4937, l, e134, K), e35._1), BigInt(1) + e35._2)
    }
    val e39 = Aalloc(l, i)
    val e139 = e39._2
    val e44 = Yalloc(j)
    val e143 = e44._2
    val e46 = Balloc(i, e44._1)
    val e147 = e46._2
    val ir = ((e36._1 + e39._1) + e46._1, ((e147 + e143) + e139) + e36._2)
    val r159 = if (l == K) {
      (ir._1, BigInt(0))
    } else {
      val e54 = fillEntryalloc(BigInt(1) + l, i, j, K)
      val e152 = e54._1
      val e55 = (ir._1, BigInt(0))
      val r158 = if (ir._1 > e152) {
        (ir._1, e55._2)
      } else {
        (e152, e55._2)
      }
      (r158._1, r158._2 + e54._2)
    }
    (r159._1, (((r159._2 + e147) + e143) + e139) + e36._2)
  }
  
  @invstate
  @memoize
  def viterbialloc(i : BigInt, j : BigInt, K : BigInt): (BigInt, BigInt) = {
    val bd = if (j == BigInt(0)) {
      val e15 = Calloc(i)
      val e19 = Yalloc(BigInt(0))
      val e21 = Balloc(i, e19._1)
      (e15._1 + e21._1, (e21._2 + e19._2) + e15._2)
    } else {
      val e27 = fillEntryalloc(BigInt(0), i, j, K)
      (e27._1, e27._2)
    }
    (bd._1, bd._2)
  }
  
  def invokealloc(i : BigInt, j : BigInt, K : BigInt): (BigInt, BigInt) = {
    val lr1 = lookup[BigInt](List(4937, i, j, K))
    val bd2 = if (lr1._1) {
      (lr1._2, BigInt(0))
    } else {
      val e62 = viterbialloc(i, j, K)
      (update[BigInt](List(4937, i, j, K), e62._1), BigInt(1) + e62._2)
    }
    (bd2._1, bd2._2)
  }
  
  def fillColumnalloc(i : BigInt, j : BigInt, K : BigInt): (List[BigInt], BigInt) = {
    val bd4 = if (i == K) {
      val e70 = invokealloc(i, j, K)
      (List[BigInt](e70._1), BigInt(2) + e70._2)
    } else {
      val e76 = invokealloc(i, j, K)
      val e82 = fillColumnalloc(BigInt(1) + i, j, K)
      (Cons[BigInt](e76._1, e82._1), (BigInt(1) + e82._2) + e76._2)
    }
    (bd4._1, bd4._2)
  }
  
  @invisibleBody
  def fillTablealloc(j : BigInt, T : BigInt, K : BigInt): (List[List[BigInt]], BigInt) = {
    val bd5 = if (j == T) {
      val e90 = fillColumnalloc(BigInt(0), j, K)
      (List[List[BigInt]](e90._1), BigInt(2) + e90._2)
    } else {
      val e96 = fillColumnalloc(BigInt(0), j, K)
      val e102 = fillTablealloc(BigInt(1) + j, T, K)
      (Cons[List[BigInt]](e96._1, e102._1), (BigInt(1) + e102._2) + e96._2)
    }
    (bd5._1, bd5._2)
  }
  
  def viterbiSolsalloc(T : BigInt, K : BigInt): (List[List[BigInt]], BigInt) = {
    val e66 = fillTablealloc(BigInt(0), T, K)
    (e66._1, e66._2)
  }

  // def main(args: Array[String]): Unit = {
  //   val points = (0 to 100 by 5) ++ (100 to 300 by 100) //++ (1000 to 10000 by 1000)
  //   // val size = points.map(x => BigInt(x)).to[scalaList]
  //   val size = points.map(x => (x)).toList
  //   var ops = List[BigInt]()
  //   var orb = List[BigInt]()
  //   var valuefori = scalaList[BigInt]()
  //   var valuefori2 = scalaList[BigInt]()
  //   var valuefori3 = scalaList[BigInt]()
    
  //   points.foreach { i =>
  //     val input = i
  //     ops :+= {
  //         leon.mem.clearMemo()
  //         viterbiSolsalloc(i, i)._2
  //      }
  //      orb :+= {2*i*i + 6*i + 5}
  //      valuefori :+= {BigInt(i)}
  //      valuefori2 :+= {BigInt(i*i)}
  //      valuefori3 :+= {BigInt(i*i*i)}
  //   }

  // //alloc <= ((2 * (K * T) + 2 * K) + 4 * T) + 5
  //   dumpdata(size, ops, orb, "viterbi", "orb")
  //   // minresults(ops, scalaList(5, 4, 2, 2), List("constant", "T", "K", "T*K"), List(valuefori, valuefori, valuefori2), size, "viterbi")
  // } 
  
     /**
   * Benchmark specific parameters
   */
  def coeffs = scalaList[BigInt](5, 4, 2, 2) //from lower to higher-order terms
  def coeffNames = List("constant", "T", "K", "T*K")
  val termsSize = 3 // number of terms (i.e monomials) in the template
  def getTermsForPoint(i: BigInt) = {    
    scalaList(i, i, i*i) 
  }  
  def inputFromPoint(i: Int) = {
    i
  }
  val dirname = "alloc/Viterbi"
  val filePrefix = "vit"
  val points =  (0 to 100 by 5)   
  val concreteInstFun = (i: BigInt) => viterbiSolsalloc(i, i)._2
  
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

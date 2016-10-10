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

object WeightedSched {
  abstract class IList
  
  case class Cons(x : BigInt, tail : IList) extends IList
  
  case class Nil() extends IList

  var jobs = Array[(BigInt, BigInt, BigInt)]()
  
  def jobInfotime(i : BigInt): ((BigInt, BigInt, BigInt), BigInt) = ((jobs(i.toInt), 1) : ((BigInt, BigInt, BigInt), BigInt))

  var p = Array[BigInt]()

  def prevCompatibleJobtime(i : BigInt): (BigInt, BigInt) = ((p(i.toInt), 1) : (BigInt, BigInt))
  
  def jobInfoalloc(i : BigInt): ((BigInt, BigInt, BigInt), BigInt) = (((0, 0, 0), 0) : ((BigInt, BigInt, BigInt), BigInt))

  def prevCompatibleJoballoc(i : BigInt): (BigInt, BigInt) = ((0, 0) : (BigInt, BigInt))
  
  @invisibleBody
  @invstate
  @memoize
  def schedalloc(jobIndex : BigInt): (BigInt, BigInt) = {
    val e31 = jobInfoalloc(jobIndex)
    val ir1 = {
      val (st, fn, w) = e31._1
      ((st, fn, w), e31._2)
    }
    val ir20 = ir1._1._3
    val r162 = if (jobIndex == BigInt(0)) {
      (ir20, BigInt(0))
    } else {
      val e67 = jobIndex - BigInt(1)
      val lr1 = lookup[BigInt](List(4875, e67))
      val ir5 = if (lr1._1) {
        (lr1._2, BigInt(0))
      } else {
        val e41 = schedalloc(e67)
        (update[BigInt](List(4875, e67), e41._1), BigInt(1) + e41._2)
      }
      val e43 = prevCompatibleJoballoc(jobIndex)
      val e72 = e43._2
      val e71 = e43._1
      val lr2 = lookup[BigInt](List(4875, e71))
      val ir6 = if (lr2._1) {
        (lr2._2, e72)
      } else {
        val e45 = schedalloc(e71)
        (update[BigInt](List(4875, e71), e45._1), (BigInt(1) + e45._2) + e72)
      }
      val e47 = (ir6._1, BigInt(0))
      val ir7 = (ir20 + ir6._1, e47._2)
      val c10 = (ir7._1 >= ir5._1, BigInt(0))
      val r159 = if (ir7._1 >= ir5._1) {
        (ir7._1, c10._2)
      } else {
        (ir5._1, c10._2)
      }
      (r159._1, ((r159._2 + e47._2) + ir6._2) + ir5._2)
    }
    (r162._1, r162._2 + ir1._2)
  }
  
  @invisibleBody
  def invokealloc(jobIndex : BigInt): (BigInt, BigInt) = {
    val lr = lookup[BigInt](List(4875, jobIndex))
    val bd = if (lr._1) {
      (lr._2, BigInt(0))
    } else {
      val e15 = schedalloc(jobIndex)
      (update[BigInt](List(4875, jobIndex), e15._1), BigInt(1) + e15._2)
    }
    (bd._1, bd._2)
  }
  
  @invisibleBody
  def schedBUalloc(jobi : BigInt): (IList, BigInt) = {
    val bd1 = if (jobi == BigInt(0)) {
      val e17 = invokealloc(jobi)
      (Cons(e17._1, Nil()), BigInt(2) + e17._2)
    } else {
      val e23 = schedBUalloc(jobi - BigInt(1))
      val e25 = invokealloc(jobi)
      (Cons(e25._1, e23._1), (BigInt(1) + e25._2) + e23._2)
    }
    (bd1._1, bd1._2)
  }
  
  // def main(args: Array[String]): Unit = {
  //   import scala.util.Random
  //   val rand = Random

  //   val points = (0 to 20 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    
  //   val size = points.map(x => (x)).toList
    
  //   var ops = List[BigInt]()
  //   var orb = List[BigInt]()
  //   points.foreach { i =>
  //     val input = i
  //     ops :+= {
  //         // 2*i+3
  //         leon.mem.clearMemo()
  //         schedBUalloc(input)._2
  //     }
  //     orb :+= {2*i + 3}
  //   }
  //   dumpdata(size, ops, orb, "wsched", "orb")
  //   // minresults(ops, scalaList(3, 3), List("constant", "jobi"), List(size), size, "wsched")
  // }

  // initialize the global input data
  jobs = Array[(BigInt, BigInt, BigInt)]()
  jobs :+= { (BigInt(0), BigInt(0), BigInt(0)) }
  (1 to 10001).foreach { n =>
    jobs :+= { (BigInt(n), BigInt(n + 2), BigInt(n)) }
  }

  p = Array[BigInt]()
  p :+= { BigInt(0) }
  p :+= { BigInt(0) }
  (2 to 10001).foreach { n =>
    p :+= { BigInt(n - 2) }
  }
  
    /**
   * Benchmark specific parameters
   */
  def coeffs = scalaList[BigInt](3, 2) //from lower to higher-order terms
  def coeffNames = List("constant", "jobi") // names of the coefficients
  val termsSize = 1 // number of terms (i.e monomials) in the template
  def getTermsForPoint(i: BigInt) = {    
    scalaList(i) 
  }
  
  def inputFromPoint(i: Int) = {
    i
  }
  val dirname = "alloc/WeightedScheduling"
  val filePrefix = "ws"
  val points =  (0 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)  
  val concreteInstFun = (input: BigInt) => schedBUalloc(input)._2
  
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

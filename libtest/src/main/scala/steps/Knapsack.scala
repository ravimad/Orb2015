package stepsAnalysis

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
  def maxValuetime(items : IList, w : BigInt, currList : IList): (BigInt, BigInt) = {
    val bd = currList match {
      case Cons((wi, vi), tail) =>
        val e17 = maxValuetime(items, w, tail)
        val e68 = e17._1
        val c13 = BigInt(3)
        val r159 = if (wi <= w && wi > BigInt(0)) {
          val e74 = w - wi
          val lr = lookup[BigInt](List(4867, e74, items))
          val e24 = if (lr._1) {
            (lr._2, BigInt(2))
          } else {
            val e23 = knapSacktime(e74, items)
            (update[BigInt](List(4867, e74, items), e23._1), BigInt(4) + e23._2)
          }
          val ir1 = (vi + e24._1, BigInt(1) + e24._2)
          val c9 = (ir1._1 >= e68, BigInt(1))
          val r158 = if (ir1._1 >= e68) {
            (ir1._1, BigInt(1) + c9._2)
          } else {
            (e68, BigInt(1) + c9._2)
          }
          (r158._1, ((BigInt(2) + c13) + r158._2) + e24._2)
        } else {
          (e68, BigInt(1) + c13)
        }
        (r159._1, (BigInt(8) + r159._2) + e17._2)
      case Nil() =>
        (BigInt(0), BigInt(5))
    }
    (bd._1, bd._2)
  }
  
  @memoize
  def knapSacktime(w : BigInt, items : IList): (BigInt, BigInt) = {
    val bd2 = if (w == BigInt(0)) {
      (BigInt(0), BigInt(2))
    } else {
      val e39 = maxValuetime(items, w, items)
      (e39._1, BigInt(3) + e39._2)
    }
    (bd2._1, bd2._2)
  }
  
  @invisibleBody
  def invoketime(i : BigInt, items : IList): (BigInt, BigInt) = {
    val lr1 = lookup[BigInt](List(4867, i, items))
    val bd1 = if (lr1._1) {
      (lr1._2, BigInt(1))
    } else {
      val e35 = knapSacktime(i, items)
      (update[BigInt](List(4867, i, items), e35._1), BigInt(3) + e35._2)
    }
    (bd1._1, bd1._2)
  }
  
  def bottomuptime(w : BigInt, items : IList): (IList, BigInt) = {
    val bd4 = if (w == BigInt(0)) {
      val e48 = invoketime(w, items)
      (Cons((w, e48._1), Nil()), BigInt(6) + e48._2)
    } else {
      val e56 = bottomuptime(w - BigInt(1), items)
      val e60 = invoketime(w, items)
      (Cons((w, e60._1), e56._1), (BigInt(7) + e60._2) + e56._2)
    }
    (bd4._1, bd4._2)
  }
  
  def knapSackSoltime(w : BigInt, items : IList): (IList, BigInt) = {
    val e44 = bottomuptime(w, items)
    (e44._1, BigInt(1) + e44._2)
  }

//  def main(args: Array[String]): Unit = {
//    
//
//    val points = (0 to 200 by 10) ++ (100 to 1000 by 50)// ++ (1000 to 10000 by 1000)
//    val size = points.map(x => BigInt(x)).to[scalaList]
//    val size2 = points.map(x => (x)).toList
//    
//    var ops = List[BigInt]()
//    var orb = List[BigInt]()
//    var valueForw = scalaList[BigInt]()
//    var valueForitemsize = scalaList[BigInt]()
//    var valueForwitemsize = scalaList[BigInt]()
//    points.foreach { i =>
//      val w = i
//      val itemsize = w / 4
//      val input = {
//        (1 to itemsize).foldLeft[IList](Nil()) { (f, n) =>
//          Cons((rand.nextInt(itemsize), rand.nextInt(itemsize)), f)  
//        }
//      }
//      ops :+= {
//          17*w*itemsize + 14*w + 17*itemsize + 18
//          // leon.mem.clearMemo()
//          // knapSackSoltime(w, input)._2
//      }
//      orb :+= {17 * (w * itemsize) + 18 * w + 17 * itemsize + 18}
//      valueForw :+= {BigInt(w)}
//      valueForitemsize :+= {BigInt(itemsize)}
//      valueForwitemsize :+= {BigInt(w*itemsize)}
//    }
//    //17 * (w * items.size) + 18 * w + 17 * items.size + 18 /
//    dumpdata(size2, ops, orb, "knapsack", "orb")
//    minresults(ops, scalaList(18, 17, 18, 17), List("constant", "itemsize", "w", "w*itemsize"), List(valueForitemsize, valueForw, valueForwitemsize), size, "knapsack")
//  }  
  
  import scala.util.Random
  val rand = Random
      /**
   * Benchmark specific parameters
   */
  def coeffs = scalaList[BigInt](18, 17, 18, 17) //from lower to higher-order terms
  def coeffNames = List("constant", "itemsize", "w", "w*timesize") // names of the coefficients
  val termsSize = 3 // number of terms (i.e monomials) in the template
  def getTermsForPoint(w: BigInt) = {
    val itemsize = w / 4
    scalaList(itemsize, w, w * itemsize) 
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
  val dirname = "Knapsack"
  val filePrefix = "ks"
  val points = (0 to 200 by 10) ++ (100 to 1000 by 50)  
  val concreteInstFun = (w: BigInt, input: IList) => knapSackSoltime(w, input)._2
  
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

object IList {
  
}

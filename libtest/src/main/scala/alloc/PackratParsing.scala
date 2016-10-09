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

object PackratParsing {
  abstract class Terminal
  
  case class Open() extends Terminal
  
  case class Close() extends Terminal
  
  case class Plus() extends Terminal
  
  case class Times() extends Terminal
  
  case class Digit() extends Terminal
  
  abstract class Result
  
  case class Parsed(rest : BigInt) extends Result
  
  case class NoParse() extends Result
  
  var istring = Array[Terminal]()
  def lookupalloc(i51 : BigInt): (Terminal, BigInt) = ((istring(i51.toInt), 0) : (Terminal, BigInt))
 
  @invisibleBody
  @memoize
  @invstate
  def pAddalloc(i : BigInt): (Result, BigInt) = {
    val lr3 = lookup[Result](List(4908, i))
    val ir1 = if (lr3._1) {
      (lr3._2, BigInt(0))
    } else {
      val e52 = pMulalloc(i)
      (update[Result](List(4908, i), e52._1), BigInt(1) + e52._2)
    }
    val scr2 = (ir1._1, BigInt(0))
    val r159 = ir1._1 match {
      case Parsed(j) =>
        val c26 = BigInt(1)
        val mc5 = if (j > BigInt(0) && lookupalloc(j)._1 == Plus()) {
          val e145 = j - BigInt(1)
          val lr4 = lookup[Result](List(4907, e145))
          val scr3 = if (lr4._1) {
            (lr4._2, BigInt(0))
          } else {
            val e56 = pAddalloc(e145)
            (update[Result](List(4907, e145), e56._1), BigInt(1) + e56._2)
          }
          val th4 = scr3._1 match {
            case Parsed(rem) =>
              (Parsed(rem), BigInt(1) + scr3._2)
            case _ =>
              (ir1._1, scr3._2)
          }
          (th4._1, c26 + th4._2)
        } else {
          (ir1._1, c26)
        }
        (mc5._1, mc5._2 + scr2._2)
      case _ =>
        (ir1._1, scr2._2)
    }
    (r159._1, r159._2 + ir1._2)
  }
  
  @invisibleBody
  @memoize
  @invstate
  def pMulalloc(i : BigInt): (Result, BigInt) = {
    val lr6 = lookup[Result](List(4909, i))
    val ir2 = if (lr6._1) {
      (lr6._2, BigInt(0))
    } else {
      val e71 = pPrimalloc(i)
      (update[Result](List(4909, i), e71._1), BigInt(1) + e71._2)
    }
    val scr5 = (ir2._1, BigInt(0))
    val r160 = ir2._1 match {
      case Parsed(j) =>
        val c28 = BigInt(1)
        val mc10 = if (j > BigInt(0) && lookupalloc(j)._1 == Times()) {
          val e164 = j - BigInt(1)
          val lr7 = lookup[Result](List(4908, e164))
          val scr6 = if (lr7._1) {
            (lr7._2, BigInt(0))
          } else {
            val e75 = pMulalloc(e164)
            (update[Result](List(4908, e164), e75._1), BigInt(1) + e75._2)
          }
          val th5 = scr6._1 match {
            case Parsed(rem) =>
              (Parsed(rem), BigInt(1) + scr6._2)
            case _ =>
              (ir2._1, scr6._2)
          }
          (th5._1, c28 + th5._2)
        } else {
          (ir2._1, c28)
        }
        (mc10._1, mc10._2 + scr5._2)
      case _ =>
        (ir2._1, scr5._2)
    }
    (r160._1, r160._2 + ir2._2)
  }
  
  @invisibleBody
  @memoize
  @invstate
  def pPrimalloc(i : BigInt): (Result, BigInt) = {
    val e15 = lookupalloc(i)
    val e95 = e15._1
    val r158 = if (e95 == Digit()) {
      val th1 = if (i > BigInt(0)) {
        (Parsed(i - BigInt(1)), BigInt(1))
      } else {
        (Parsed(BigInt(-1)), BigInt(1))
      }
      (th1._1, BigInt(1) + th1._2)
    } else {
      val el3 = if (e95 == Open() && i > BigInt(0)) {
        val e105 = i - BigInt(1)
        val lr = lookup[Result](List(4907, e105))
        val scr = if (lr._1) {
          (lr._2, BigInt(0))
        } else {
          val e25 = pAddalloc(e105)
          (update[Result](List(4907, e105), e25._1), BigInt(1) + e25._2)
        }
        val th3 = scr._1 match {
          case Parsed(rem) =>
            val c22 = BigInt(1)
            val mc = if (rem >= BigInt(0) && lookupalloc(rem)._1 == Close()) {
              (Parsed(rem - BigInt(1)), BigInt(1) + c22)
            } else {
              (NoParse(), BigInt(1) + c22)
            }
            (mc._1, mc._2 + scr._2)
          case _ =>
            (NoParse(), BigInt(1) + scr._2)
        }
        (th3._1, BigInt(1) + th3._2)
      } else {
        (NoParse(), BigInt(2))
      }
      (el3._1, BigInt(1) + el3._2)
    }
    (r158._1, r158._2 + e15._2)
  }
  
  def invokePrimalloc(i : BigInt): (Result, BigInt) = {
    val lr1 = lookup[Result](List(4909, i))
    val bd1 = if (lr1._1) {
      (lr1._2, BigInt(0))
    } else {
      val e46 = pPrimalloc(i)
      (update[Result](List(4909, i), e46._1), BigInt(1) + e46._2)
    }
    (bd1._1, bd1._2)
  }
  
  def invokeMulalloc(i : BigInt): (Result, BigInt) = {
    val e67 = invokePrimalloc(i)
    val bd4 = {
      val _ = e67._1
      val lr5 = lookup[Result](List(4908, i))
      val mc7 = if (lr5._1) {
        (lr5._2, BigInt(0))
      } else {
        val e69 = pMulalloc(i)
        (update[Result](List(4908, i), e69._1), BigInt(1) + e69._2)
      }
      (mc7._1, mc7._2 + e67._2)
    }
    (bd4._1, bd4._2)
  }
  
  def invokealloc(i : BigInt): (Result, BigInt) = {
    val e48 = invokeMulalloc(i)
    val bd2 = {
      val _ = e48._1
      val lr2 = lookup[Result](List(4907, i))
      val mc2 = if (lr2._1) {
        (lr2._2, BigInt(0))
      } else {
        val e50 = pAddalloc(i)
        (update[Result](List(4907, i), e50._1), BigInt(1) + e50._2)
      }
      (mc2._1, mc2._2 + e48._2)
    }
    (bd2._1, bd2._2)
  }
  
  def parsealloc(n : BigInt): (Result, BigInt) = {
    val bd6 = if (n == BigInt(0)) {
      val e86 = invokealloc(n)
      (e86._1, e86._2)
    } else {
      val e90 = parsealloc(n - BigInt(1))
      val el6 = {
        val _ = e90._1
        val e92 = invokealloc(n)
        (e92._1, e92._2 + e90._2)
      }
      (el6._1, el6._2)
    }
    (bd6._1, bd6._2)
  }

  def genString(i: Int): Array[Terminal] = {
    var res = new Array[Terminal](4*i + 1) // Array.fill(4*i + 1){Digit()}
    var j = 0
    while(j != i) {
      res(3*j) = Open() 
      res(3*j + 1) = Digit()
      if(j%2 == 0) {
        res(3*j + 2) = Plus()
      } else {
        res(3*j + 2) = Times()
      }
      j = j + 1
    }
    res(3*i) = Digit()
    j = 0
    while(j != i) {
      res(3*i + j + 1) = Close()
      j = j + 1
    }
    return res
  
    // import scala.util.Random
    // val rand = Random

    // var res = new Array[Terminal](i + 1) // Array.fill(4*i + 1){Digit()}
    // var j = 0
    // while(j != i + 1) {
    //   var temp = rand.nextInt(5)
    //   temp match {
    //     case 0 => res(j) = Open()
    //     case 1 => res(j) = Close()
    //     case 2 => res(j) = Times()
    //     case 3 => res(j) = Plus()
    //     case 4 => res(j) = Digit()
    //   }
    //   j = j + 1
    // }
    // return res
  }
  
  // def main(args: Array[String]): Unit = {
  //   import scala.util.Random
  //   val rand = Random

  //   val points = (0 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
  //   val size = points.map(x => (x)).toList
  //   val size2 = points.map(x => BigInt(x)).to[scalaList]
    
  //   var ops = List[BigInt]()
  //   var orb = List[BigInt]()
  //   var valueFori = List[BigInt]()
  //   points.foreach { i =>
  //     val input = i
  //     ops :+= {
  //         11*i + 7
  //         // leon.mem.clearMemo()
  //         // istring = Array.fill[Terminal](i + 1)(Digit())
  //         // parsealloc(i)._2
  //     }
  //     orb :+= {11*i + 11}
  //     valueFori :+= {i}
  //   }
  //   dumpdata(size, ops, orb, "packrat", "orb")
  //   // minresults(ops, scalaList(11, 11), List("constant", "i"), List(size2), size2, "packrat")
  // }  
  /**
   * Benchmark specific parameters
   */
  def coeffs = scalaList[BigInt](11, 11) //from lower to higher-order terms
  def coeffNames = List("constant", "i") // names of the coefficients
  val termsSize = 1 // number of terms (i.e monomials) in the template
  def getTermsForPoint(i: BigInt) = {    
    scalaList(i) 
  }
  def inputFromPoint(i: Int) = {
    // fill the input string with digits
    istring = Array.fill[Terminal](i + 1)(Digit())
    i
  }
  val dirname = "alloc/PackratParsing"
  val filePrefix = "pp"
  val points =  (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)  
  val concreteInstFun = (input: BigInt) => parsealloc(input)._2
  
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

object Result {
  
}

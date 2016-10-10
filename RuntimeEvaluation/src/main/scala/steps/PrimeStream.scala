package stepsAnalysis

import leon.collection._
import leon._
import leon.mem._
import leon.higherorder._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.collection._
import leon.runtimeDriver._
import scala.collection.mutable.{ListBuffer => scalaList}

object PrimeStream {
  abstract class Bool
  
  case class True() extends Bool
  
  case class False() extends Bool
  
  
  abstract class Stream2
  
  
  case class SCons1(x318 : (BigInt, Bool), tailFun1 : () => (Stream2, BigInt)) extends Stream2
  
  
  case class SNil1() extends Stream2
  
  val primeStreamtime : (SCons1, BigInt) = (SCons1((BigInt(1), True()), () => {
    val e62 = nextElemtime(BigInt(2))
    (e62._1, BigInt(1) + e62._2)
  }), BigInt(4))
  
  def isPrimeRectime(i : BigInt, n : BigInt): (Bool, BigInt) = {
    val bd = if (i == BigInt(1)) {
      (True(), BigInt(3))
    } else {
      val c19 = BigInt(6)
      val el1 = if ({
        assert(i != BigInt(0), "Division by zero")
        n / i
      } * i == n) {
        (False(), BigInt(2) + c19)
      } else {
        val e18 = isPrimeRectime(i - BigInt(1), n)
        (e18._1, (BigInt(3) + c19) + e18._2)
      }
      (el1._1, BigInt(2) + el1._2)
    }
    (bd._1, bd._2)
  }
  
  def isPrimeNumtime(n : BigInt): (Bool, BigInt) = {
    val e57 = isPrimeRectime(n - BigInt(1), n)
    (e57._1, BigInt(2) + e57._2)
  }
  
  def nextElemtime(i : BigInt): (Stream2, BigInt) = {
    val e38 = isPrimeNumtime(i)
    val ir5 = BigInt(1) + i
    (SCons1((i, e38._1), () => {
      val e44 = nextElemtime(ir5)
      (e44._1, BigInt(1) + e44._2)
    }), BigInt(5) + e38._2)
  }
  
  def isPrimeStime(s : Stream2, i : BigInt): (Boolean, BigInt) = {
    val bd2 = s match {
      case SNil1() =>
        (true, BigInt(2))
      case SCons1(x, tfun1) =>
        val temp1 = () => {
          val e34 = nextElemtime(i)
          (e34._1, BigInt(1) + e34._2)
        }
        (tfun1 == temp1, BigInt(7))
    }
    (bd2._1, bd2._2)
  }
  
  def primesUntilNtime(n : BigInt): (List[BigInt], BigInt) = {
    val e52 = takeRectime(BigInt(0), n - BigInt(2), primeStreamtime._1)
    (e52._1, BigInt(3) + e52._2)
  }
  
  def takeRectime(i : BigInt, n : BigInt, s : Stream2): (List[BigInt], BigInt) = {
    val bd9 = s match {
      case c13 @ SCons1((x, b), _) =>
        val mc2 = if (i < n) {
          val lr = lookup[Stream2](List(4889, c13))
          val e70 = if (lr._1) {
            (lr._2, BigInt(1))
          } else {
            val e69 = Stream.tailtime(c13)
            (update[Stream2](List(4889, c13), e69._1), BigInt(3) + e69._2)
          }
          val e71 = takeRectime(BigInt(1) + i, n, e70._1)
          val r167 = if (b == True()) {
            (Cons[BigInt](x, e71._1), BigInt(4))
          } else {
            (e71._1, BigInt(3))
          }
          (r167._1, ((BigInt(4) + r167._2) + e71._2) + e70._2)
        } else {
          (List[BigInt](), BigInt(3))
        }
        (mc2._1, BigInt(6) + mc2._2)
      case _ =>
        (List[BigInt](), BigInt(5))
    }
    (bd9._1, bd9._2)
  }
  
  /**
   * Benchmark specific parameters
   */
  abstract class RunContext {
    def coeffs: scalaList[BigInt] //from lower to higher-order terms
    def coeffNames: List[String] 
    val termsSize = 1 // number of terms (i.e monomials) in the template
    def getTermsForPoint(n: BigInt): scalaList[BigInt] 
    def inputFromPoint(i: Int) = i
    val dirname = "steps/PrimeStream"
    val filePrefix: String
    val points = (2 to 100 by 5) ++ (100 to 1000 by 100)
    val concreteInstFun = (n: BigInt) => primesUntilNtime(n)._2
    val clearCache: Boolean
  }
  object QuadContext extends RunContext {
    override def coeffs = scalaList[BigInt](28, 16)
    override def coeffNames = List("constant", "n*n") // names of the coefficients
    override def getTermsForPoint(n: BigInt): scalaList[BigInt] = scalaList(n * n)
    override val filePrefix = "prims-quad"
    override val clearCache: Boolean = true
  }

  /**
   * Here, the primes is continually queried without clearing the cache.
   */
  object LinContext extends RunContext {
    override def coeffs = scalaList[BigInt](-18, 15)
    override def coeffNames = List("constant", "n") // names of the coefficients
    override def getTermsForPoint(n: BigInt): scalaList[BigInt] = scalaList(n)
    override val filePrefix = "prims-linear"
    override val clearCache: Boolean = false
  }
  val ctxts: scalaList[RunContext] = scalaList(QuadContext, LinContext)
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
      if(clearCache)
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
}

object Stream {
  def tailtime(thiss : PrimeStream.Stream2): (PrimeStream.Stream2, BigInt) = {
    val e84 = {
      assert(thiss.isInstanceOf[PrimeStream.SCons1], "Cast error")
      thiss.asInstanceOf[PrimeStream.SCons1]
    }.tailFun1()
    (e84._1, BigInt(5) + e84._2)
  }
}


package stepsAnalysis

import leon.collection._
import leon._
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.instrumentation._
import leon.invariant._
import leon.runtimeDriver._
import scala.collection.mutable.{ ListBuffer => scalaList }


object RedBlackTree {
  abstract class Color
  
  case class Red() extends Color
  
  case class Black() extends Color
  
  abstract class Tree
  
  case class Empty() extends Tree
  
  case class Node(color : Color, left : Tree, value : BigInt, right : Tree) extends Tree
  
  def insRecsteps(x : BigInt, t : Tree): (Tree, BigInt) = {
    val bd$1 = t match {
      case Empty() =>
        (Node(Red(), Empty(), x, Empty()), BigInt(6))
      case Node(c, a, y, b) =>
        val mc$1 = if (x < y) {
          val e$42 = insRecsteps(x, a)
          val e$47 = balancesteps(c, e$42._1, y, b)
          (e$47._1, (BigInt(4) + e$47._2) + e$42._2)
        } else {
          val el$1 = if (x == y) {
            (Node(c, a, y, b), BigInt(3))
          } else {
            val e$54 = insRecsteps(x, b)
            val e$59 = balancesteps(c, a, y, e$54._1)
            (e$59._1, (BigInt(4) + e$59._2) + e$54._2)
          }
          (el$1._1, BigInt(2) + el$1._2)
        }
        (mc$1._1, BigInt(7) + mc$1._2)
    }
    (bd$1._1, bd$1._2)
  }
  
  def makeBlacksteps(n : Tree): (Tree, BigInt) = {
    val bd$2 = n match {
      case Node(Red(), l, v, r) =>
        (Node(Black(), l, v, r), BigInt(9))
      case _ =>
        (n, BigInt(4))
    }
    (bd$2._1, bd$2._2)
  }
  
  def inssteps(x : BigInt, t : Tree): (Tree, BigInt) = {
    val e$33 = insRecsteps(x, t)
    val e$35 = makeBlacksteps(e$33._1)
    (e$35._1, (BigInt(2) + e$35._2) + e$33._2)
  }
  
  def balancesteps(co : Color, l : Tree, x : BigInt, r : Tree): (Tree, BigInt) = {
    val bd$3 = Node(co, l, x, r) match {
      case Node(Black(), Node(Red(), Node(Red(), a, xV, b), yV, c), zV, d) =>
        (Node(Red(), Node(Black(), a, xV, b), yV, Node(Black(), c, zV, d)), BigInt(26))
      case Node(Black(), Node(Red(), a, xV, Node(Red(), b, yV, c)), zV, d) =>
        (Node(Red(), Node(Black(), a, xV, b), yV, Node(Black(), c, zV, d)), BigInt(37))
      case Node(Black(), a, xV, Node(Red(), Node(Red(), b, yV, c), zV, d)) =>
        (Node(Red(), Node(Black(), a, xV, b), yV, Node(Black(), c, zV, d)), BigInt(48))
      case Node(Black(), a, xV, Node(Red(), b, yV, Node(Red(), c, zV, d))) =>
        (Node(Red(), Node(Black(), a, xV, b), yV, Node(Black(), c, zV, d)), BigInt(59))
      case _ =>
        (Node(co, l, x, r), BigInt(47))
    }
    (bd$3._1, bd$3._2)
  }

  def log(x: BigInt): BigInt = {
    if (x <= 1) BigInt(0)
    else 1 + log(x/2)
  } 

  def size(t: Tree): BigInt = {  
    (t match {
      case Empty() => BigInt(0)
      case Node(_, l, v, r) => size(l) + 1 + size(r)
    })
  }

  def maxHeightNode(t: Tree): Tree = {
    t match {      
      case Empty() =>  t
      case n@Node(_, Empty(), _, Empty()) => n
      case Node(_, l, _, r) =>  maxHeightNode(r)         
    }
  }

 var itosize: Map[BigInt, BigInt] = Map() 
    /**
   * Benchmark specific parameters
   */
   import scala.util.Random
  abstract class RunContext {
    def coeffs: scalaList[BigInt] //from lower to higher-order terms
    def coeffNames = List("constant","logsize") // names of the coefficients
    val termsSize = 1 // number of terms (i.e monomials) in the template
    def getTermsForPoint(i: BigInt): scalaList[BigInt] = {      
      scalaList(i)
      //scalaList(log(itosize(i)+1))
    }
    def inputFromPoint(i: Int) = {      
      val len = i // i here represents the blackHeight      
      val maxnumnodes = BigInt(1) << len
      var leafNum = BigInt(0) 

      def skewdRBT(pathlen: Int, nindex: Int): Node = {
        // we need red color at odd indices and black at even indices
        if(nindex == pathlen) {
          leafNum += maxnumnodes 
          Node(Black(), Empty(), leafNum, Empty())
        } else {
          if(nindex % 2 == 0) {
             // even
             val left: Node = neatRBT((pathlen - nindex)/2, 1)
             val right: Node = skewdRBT(pathlen, nindex + 1)
             Node(Black(), left, left.value + 1, right)
          } else {
            // odd          
             val left: Node = neatRBT((pathlen - nindex)/2 + 1, 1)
             val right: Node = skewdRBT(pathlen, nindex + 1)
             Node(Red(), left, left.value + 1, right)
          }          
        }
      }

      def neatRBT(pathlen: Int, nindex: Int): Node = {
        if(nindex == pathlen) {
          leafNum += maxnumnodes 
          Node(Black(), Empty(), leafNum, Empty())
        } else {
          val left: Node = neatRBT(pathlen, nindex + 1)
          val right: Node = neatRBT(pathlen, nindex + 1)
          Node(Black(), left, left.value + 1, right)
        }
      }
      val rbt = skewdRBT(2 * len, 1)
      itosize += (BigInt(i) -> size(rbt))
      rbt
    }
    val dirname = "steps/RedBlackTree"
    val filePrefix: String
    val points = (1 to 20)
    val concreteInstFun: Tree => BigInt
  }
  object insContext extends RunContext {
    override def coeffs = scalaList[BigInt](66, 132)
    override val filePrefix = "rbt" // the abbrevation used in the paper
    override val concreteInstFun = (rbt: Tree) => {
      // find the node in the tree of maximum height and insert the max + 1  
      val mn = maxHeightNode(rbt).asInstanceOf[Node]      
      val maxval = mn.value
      println("Max value: "+maxval)   
      inssteps(maxval + 1, rbt)._2
    }
  }

  val ctxts: scalaList[RunContext] = scalaList(insContext)
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
}

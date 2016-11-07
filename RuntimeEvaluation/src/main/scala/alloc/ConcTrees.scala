package allocAnalysis

import leon.collection._
import leon.instrumentation._
import leon.collection._
import leon.lang._
import leon.collection.ListSpecs._
import leon.annotation._
import leon.invariant._
import scala.collection.mutable.{ ListBuffer => scalaList }
import leon.runtimeDriver._

object ConcTrees {
  @inline
  def max(x: BigInt, y: BigInt): BigInt = if (x >= y) x else y

  abstract class Conc[T] {
    val size: BigInt = {
      (this match {
        case Empty()   => 0
        case Single(x) => 1
        case CC(l, r) =>
          l.size + r.size
      }): BigInt
    } ensuring (_ >= 0)

    val level: BigInt = {
      (this match {
        case Empty()   => 0
        case Single(x) => 0
        case CC(l, r) =>
          1 + max(l.level, r.level)
      }): BigInt
    } ensuring (_ >= 0)
  }

  case class Empty[T]() extends Conc[T]

  case class Single[T](x : T) extends Conc[T]

  case class CC[T](left : Conc[T], right : Conc[T]) extends Conc[T]

  @invisibleBody
  def lookupalloc[T](xs : Conc[T], i : BigInt): (T, BigInt) = {
    val bd3 = xs match {
      case Single(x) =>
        (x, BigInt(0))
      case CC(l, r) =>
        val mc10 = if (i < (l.size)) {
          val e144 = lookupalloc[T](l, i)
          (e144._1, e144._2)
        } else {
          val e151 = lookupalloc[T](r, i - (l.size))
          (e151._1, e151._2)
        }
        (mc10._1, mc10._2)
    }
    (bd3._1, bd3._2)
  }

  @invisibleBody
  def updatealloc[T](xs : Conc[T], i : BigInt, y : T): (Conc[T], BigInt) = {
    val bd1 = xs match {
      case Single(x) =>
        (Single[T](y), BigInt(1))
      case CC(l, r) =>
        val mc5 = if (i < (l.size)) {
          val e94 = updatealloc[T](l, i, y)
          (CC[T](e94._1, r), BigInt(1) + e94._2)
        } else {
          val e105 = updatealloc[T](r, i - (l.size), y)
          (CC[T](l, e105._1), BigInt(1) + e105._2)
        }
        (mc5._1, mc5._2)
    }
    (bd1._1, bd1._2)
  }

  @invisibleBody
  def concatNonEmptyalloc[T](xs : Conc[T], ys : Conc[T]): (Conc[T], BigInt) = {
    val ir34 = (ys.level) - (xs.level)
    val r185 = if (ir34 >= BigInt(-1) && ir34 <= BigInt(1)) {
      (CC[T](xs, ys), BigInt(1))
    } else {
      val el5 = if (ir34 < BigInt(-1)) {
        val th3 = {
          val CC(l, r) = xs
          val mc1 = if ((l.level) >= (r.level)) {
            val e25 = concatNonEmptyalloc[T](r, ys)
            (CC[T](l, e25._1), BigInt(1) + e25._2)
          } else {
            val el1 = {
              val CC(rl, rr) = r
              val e29 = concatNonEmptyalloc[T](rr, ys)
              val e400 = e29._1
              val r183 = if ((e400.level) == (xs.level) - BigInt(3)) {
                (CC[T](l, CC[T](rl, e400)), BigInt(2))
              } else {
                (CC[T](CC[T](l, rl), e400), BigInt(2))
              }
              (r183._1, r183._2 + e29._2)
            }
            (el1._1, el1._2)
          }
          (mc1._1, mc1._2)
        }
        (th3._1, th3._2)
      } else {
        val el4 = {
          val CC(l, r) = ys
          val mc3 = if ((r.level) >= (l.level)) {
            val e54 = concatNonEmptyalloc[T](xs, l)
            (CC[T](e54._1, r), BigInt(1) + e54._2)
          } else {
            val el3 = {
              val CC(ll, lr) = l
              val e59 = concatNonEmptyalloc[T](xs, ll)
              val e420 = e59._1
              val r184 = if ((e420.level) == (ys.level) - BigInt(3)) {
                (CC[T](CC[T](e420, lr), r), BigInt(2))
              } else {
                (CC[T](e420, CC[T](lr, r)), BigInt(2))
              }
              (r184._1, r184._2 + e59._2)
            }
            (el3._1, el3._2)
          }
          (mc3._1, mc3._2)
        }
        (el4._1, el4._2)
      }
      (el5._1, el5._2)
    }
    (r185._1, r185._2)
  }

  @invisibleBody
  def concatNormalizedalloc[T](xs : Conc[T], ys : Conc[T]): (Conc[T], BigInt) = {
    val bd11 = (xs, ys) match {
      case (xs, Empty()) =>
        (xs, BigInt(0))
      case (Empty(), ys) =>
        (ys, BigInt(0))
      case _ =>
        val e272 = concatNonEmptyalloc[T](xs, ys)
        (e272._1, e272._2)
    }
    (bd11._1, bd11._2)
  }

  @invisibleBody
  def insertalloc[T](xs : Conc[T], i : BigInt, y : T): (Conc[T], BigInt) = {
    val bd2 = xs match {
      case Empty() =>
        (Single[T](y), BigInt(1))
      case Single(x) =>
        val mc7 = if (i == BigInt(0)) {
          (CC[T](Single[T](y), xs), BigInt(2))
        } else {
          (CC[T](xs, Single[T](y)), BigInt(2))
        }
        (mc7._1, mc7._2)
      case CC(l, r) =>
        val mc8 = if (i < (l.size)) {
          val e123 = insertalloc[T](l, i, y)
          val e126 = concatNonEmptyalloc[T](e123._1, r)
          (e126._1, e126._2 + e123._2)
        } else {
          val e135 = insertalloc[T](r, i - (l.size), y)
          val e137 = concatNonEmptyalloc[T](l, e135._1)
          (e137._1, e137._2 + e135._2)
        }
        (mc8._1, mc8._2)
    }
    (bd2._1, bd2._2)
  }

  @invisibleBody
  def splitalloc[T](xs : Conc[T], n : BigInt): ((Conc[T], Conc[T]), BigInt) = {
    val bd4 = xs match {
      case Empty() =>
        ((Empty[T](), Empty[T]()), BigInt(2))
      case s @ Single(x) =>
        val mc12 = if (n <= BigInt(0)) {
          ((Empty[T](), s), BigInt(1))
        } else {
          ((s, Empty[T]()), BigInt(1))
        }
        (mc12._1, mc12._2)
      case CC(l, r) =>
        val mc15 = if (n < (l.size)) {
          val e166 = splitalloc[T](l, n)
          val ir3 = {
            val (ll, lr) = e166._1
            ((ll, lr), e166._2)
          }
          val ir18 = ir3._1
          val e174 = concatNormalizedalloc[T](ir18._2, r)
          ((ir18._1, e174._1), e174._2 + ir3._2)
        } else {
          val el12 = if (n > (l.size)) {
            val e182 = splitalloc[T](r, n - (l.size))
            val ir6 = {
              val (rl, rr) = e182._1
              ((rl, rr), e182._2)
            }
            val ir24 = ir6._1
            val e189 = concatNormalizedalloc[T](l, ir24._1)
            ((e189._1, ir24._2), e189._2 + ir6._2)
          } else {
            ((l, r), BigInt(0))
          }
          (el12._1, el12._2)
        }
        (mc15._1, mc15._2)
    }
    (bd4._1, bd4._2)
  }

  /**
   * Benchmark specific parameters
   */
  abstract class RunContext {
    def coeffs: scalaList[BigInt] //from lower to higher-order terms
    def coeffNames = List("constant", "abs(xs.lvl-ys.lvl)") // names of the coefficients
    val termsSize = 1 // number of terms (i.e monomials) in the template
    def getTermsForPoint(i: Int): scalaList[BigInt] = {
      val treei = inputFromPoint(i)
      scalaList(treei.level - Single[BigInt](BigInt(0)).level) // ys is fixed a single element tree to get worst case
    }
    def inputFromPoint(i: Int) = {
      val len = ((1 << i) - 1)
      var contree: Conc[BigInt] = Single[BigInt](BigInt(0))
      for (i <- 0 until len) {
        contree = insertalloc(contree, BigInt(0), BigInt(0))._1
      }
      contree
    }
    val dirname = "alloc/Conqueue"
    val filePrefix: String
    val points = (1 to 20) // increase upto 21 if needed
    val concreteInstFun: Conc[BigInt] => BigInt
  }
  object ConcatContext extends RunContext {
    override def coeffs = scalaList[BigInt](1, 2)
    override val filePrefix = "conq-concat" // the abbrevation used in the paper
    override val concreteInstFun = (contree: Conc[BigInt]) => concatNonEmptyalloc(contree, Single[BigInt](BigInt(0)))._2
  }
  val concCtxts: scalaList[RunContext] = scalaList(ConcatContext)
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
    concCtxts.foreach(benchmark)
  }
}

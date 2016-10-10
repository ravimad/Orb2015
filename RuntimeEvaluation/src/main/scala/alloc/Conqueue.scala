package allocAnalysis

import leon.collection._
import leon._
import leon.collection._
import leon.mem._
import leon.higherorder._
import leon.lang._
import leon.math._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import allocAnalysis.ConcTrees._
import leon.runtimeDriver._
import scala.collection.mutable.{ ListBuffer => scalaList }

object Conqueue {

  abstract class ConList2[T]

  case class Tip1[T](t405: Conc[T]) extends ConList2[T]

  case class Spine1[T](head58: Conc[T], rear65: Stream2[T]) extends ConList2[T]

  abstract class Stream2[T]

  case class Val1[T](x372: ConList2[T]) extends Stream2[T]

  case class Susp1[T](fun13: () => (ConList2[T], BigInt)) extends Stream2[T]

  case class Conqueue3[T](trees11: Stream2[T], schedule11: List[Stream2[T]])

  def emptyNum[T] = Conqueue3[T](Val1(Tip1(Empty[T]())), Nil())

  @invisibleBody
  def pushLeftStreamalloc[T](ys: Single[T], xs: Stream2[T]): (ConList2[T], BigInt) = {
    val e274 = Stream.getalloc[T](xs)
    val e443 = e274._2
    val bd12 = e274._1 match {
      case Tip1(_: CC[T]) =>
        (Spine1[T](ys, xs), BigInt(1) + e443)
      case Tip1(Empty()) =>
        (Tip1[T](ys), BigInt(1) + e443)
      case Tip1(t @ Single(_)) =>
        (Tip1[T](CC[T](ys, t)), BigInt(2) + e443)
      case s79 @ Spine1(Empty(), rear125) =>
        (Spine1[T](ys, rear125), BigInt(1) + e443)
      case s80 @ Spine1(_, _) =>
        val e285 = pushLeftLazyalloc[T](ys, xs)
        (e285._1, e285._2 + e443)
    }
    (bd12._1, bd12._2)
  }

  @invisibleBody
  @invstate
  def pushLeftLazyalloc[T](ys: Conc[T], xs: Stream2[T]): (ConList2[T], BigInt) = {
    val e232 = Stream.getalloc[T](xs)
    val bd10 = {
      val Spine1(head, rear109) = e232._1
      val ir16 = CC[T](head, ys)
      val e236 = Stream.getalloc[T](rear109)
      val e301 = e236._2
      val r199 = e236._1 match {
        case Tip1(tree) =>
          val mc24 = if ((tree.level) > (ir16.level)) {
            (Spine1[T](Empty[T](), Val1[T](Spine1[T](ir16, rear109))), BigInt(4))
          } else {
            (Spine1[T](Empty[T](), Val1[T](Spine1[T](Empty[T](), Val1[T](Tip1[T](CC[T](tree, ir16)))))), BigInt(8))
          }
          (mc24._1, mc24._2 + e301)
        case Spine1(Empty(), srearfun1) =>
          (Spine1[T](Empty[T](), Val1[T](Spine1[T](ir16, srearfun1))), BigInt(4) + e301)
        case s78 =>
          (Spine1[T](Empty[T](), Susp1[T](() => {
            val e265 = pushLeftLazyalloc[T](ir16, rear109)
            (e265._1, e265._2)
          })), BigInt(4) + e301)
      }
      (r199._1, (BigInt(1) + r199._2) + e232._2)
    }
    (bd10._1, bd10._2)
  }

  @invisibleBody
  def pushLeftalloc[T](ys: Single[T], w: Conqueue3[T]): ((Stream2[T], List[Stream2[T]]), BigInt) = {
    val e205 = pushLeftStreamalloc[T](ys, w.trees11)
    val e466 = e205._1
    val ir10 = e466 match {
      case Spine1(Empty(), rear100: Susp1[T]) =>
        (Cons[Stream2[T]](rear100, w.schedule11), BigInt(1))
      case _ =>
        (w.schedule11, BigInt(0))
    }
    ((Val1[T](e466), ir10._1), (BigInt(1) + ir10._2) + e205._2)
  }

  @invisibleBody
  def Payalloc[T](q: Stream2[T], scheds: List[Stream2[T]]): (List[Stream2[T]], BigInt) = {
    val bd7 = scheds match {
      case c22 @ Cons(head85, rest12) =>
        val e216 = Stream.getalloc[T](head85)
        val e439 = e216._2
        val mc21 = e216._1 match {
          case Spine1(Empty(), rear103: Susp1[T]) =>
            (Cons[Stream2[T]](rear103, rest12), BigInt(1) + e439)
          case _ =>
            (rest12, e439)
        }
        (mc21._1, mc21._2)
      case Nil() =>
        (scheds, BigInt(0))
    }
    (bd7._1, bd7._2)
  }

  @invisibleBody
  def pushLeftAndPayalloc[T](ys: Single[T], w: Conqueue3[T]): (Conqueue3[T], BigInt) = {
    val e221 = pushLeftalloc[T](ys, w)
    val ir11 = {
      val (q, scheds) = e221._1
      ((q, scheds), e221._2)
    }
    val ir40 = ir11._1
    val ir46 = ir40._1
    val e228 = Payalloc[T](ir46, ir40._2)
    (Conqueue3[T](ir46, e228._1), (BigInt(1) + e228._2) + ir11._2)
  }

  //  def main(args: Array[String]): Unit = {
  //    import scala.util.Random
  //    val rand = Random
  //
  //    val points = (0 to 21)
  //    val size = points.map(x => ((1 << x) - 1)).toList
  //    val size2 = points.map(x => (BigInt((1 << x) - 1))).to[scalaList]
  //
  //    var ops = List[BigInt]()
  //    var orb = List[BigInt]()
  //    var abssubs = scalaList[BigInt]()
  //    size.foreach { length =>
  //      var temptree:Conc[BigInt] = Single[BigInt](BigInt(0))
  //      for (i <- 0 until length) {
  //        temptree = insertalloc(temptree, BigInt(0), BigInt(0))._1
  //      }
  //      // temptree = concatNonEmptyalloc(temptree, Single[BigInt](BigInt(0)))._1
  //      ops :+= {1*(temptree.level - Single[BigInt](BigInt(0)).level) + 1}
  //      orb :+= {2 * (temptree.level - Single[BigInt](BigInt(0)).level) + 1}
  //      abssubs :+= {(temptree.level - Single[BigInt](BigInt(0)).level)}
  //
  //    }
  //    dumpdata(size, ops, orb, "concatNonEmpty", "orb")
  //    minresults(ops, scalaList(1, 2), List("constant", "abs(x - y)"), List(abssubs), size2, "concatNonEmpty")
  //
  //    ops = List[BigInt]()
  //    orb = List[BigInt]()
  //    size.foreach { length =>
  //      var tempqueue = emptyNum[BigInt]
  //      for (i <- 0 until length) {
  //        tempqueue = pushLeftAndPayalloc(Single[BigInt](BigInt(0)), tempqueue)._1
  //      }
  //      ops :+= {pushLeftAndPayalloc(Single[BigInt](BigInt(0)), tempqueue)._2}
  //      orb :+= {23}
  //    }
  //    dumpdata(size, ops, orb, "pushLeftAndPay", "orb")
  //    minresults(ops, scalaList(23), List("constant"), List(), size2, "pushLeftAndPay")
  //
  //  }

  object Stream {
    def fvalalloc[T](thiss: Conqueue.Stream2[T]): (Conqueue.ConList2[T], BigInt) = {
      val bd6 = {
        val Conqueue.Susp1(f124) = thiss
        val e214 = f124()
        (e214._1, e214._2)
      }
      (bd6._1, bd6._2)
    }

    def getalloc[T](thiss: Conqueue.Stream2[T]): (Conqueue.ConList2[T], BigInt) = {
      val bd13 = thiss match {
        case Conqueue.Susp1(f127) =>
          val lr4 = lookup[Conqueue.ConList2[T]](List(6433, thiss))
          val mc36 = if (lr4._1) {
            (lr4._2, BigInt(0))
          } else {
            val e287 = fvalalloc[T](thiss)
            (update[Conqueue.ConList2[T]](List(6433, thiss), e287._1), BigInt(1) + e287._2)
          }
          (mc36._1, mc36._2)
        case Conqueue.Val1(x395) =>
          (x395, BigInt(0))
      }
      (bd13._1, bd13._2)
    }
  }

  /**
   * Benchmark specific parameters
   */
  abstract class RunContext {
    def coeffs: scalaList[BigInt] //from lower to higher-order terms
    def coeffNames = List("constant") // names of the coefficients
    val termsSize = 0 // number of terms (i.e monomials) in the template
    def getTermsForPoint(i: BigInt): scalaList[BigInt] = scalaList()
    def inputFromPoint(i: Int) = {
      val len = ((1 << i) - 1)
      var conq = emptyNum[BigInt]
      for (i <- 0 until len) {
        conq = pushLeftAndPayalloc(Single[BigInt](BigInt(0)), conq)._1
      }
      conq
    }
    val dirname = "alloc/Conqueue"
    val filePrefix: String
    val points = (0 to 19) // increase to 21 for more precision
    val concreteInstFun: Conqueue3[BigInt] => BigInt
  }
  object PushContext extends RunContext {
    override def coeffs = scalaList[BigInt](23)
    override val filePrefix = "conq-push" // the abbrevation used in the paper
    override val concreteInstFun = (conq: Conqueue3[BigInt]) => pushLeftAndPayalloc(Single[BigInt](BigInt(0)), conq)._2
  }
  val ctxts: scalaList[RunContext] = scalaList(PushContext)
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

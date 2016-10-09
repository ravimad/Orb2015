package stepsAnalysis

import leon.collection._
import leon._
import leon.mem._
import leon.higherorder._
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.instrumentation._
import leon.math._
import leon.invariant._
import leon.runtimeDriver._
import scala.collection.mutable.{ListBuffer => scalaList}

object Deque {
  
  abstract class Stream2[T]
  
  
  case class SCons1[T](x442 : T, next64 : ValOrFun2[T]) extends Stream2[T]
  
  
  case class SNil1[T]() extends Stream2[T]
  
  
  abstract class ValOrFun2[T]
  
  
  case class Val1[T](x440 : Stream2[T]) extends ValOrFun2[T]
  
  
  case class Fun3[T](fun23 : () => (Stream2[T], BigInt)) extends ValOrFun2[T]
  
  
  case class Queue2[T](f226 : Stream2[T], lenf76 : BigInt, sf74 : Stream2[T], r237 : Stream2[T], lenr76 : BigInt, sr74 : Stream2[T])
  
  @invstate
  def takeLazytime[T](n : BigInt, l : Stream2[T]): (Stream2[T], BigInt) = {
    val bd14 = {
      val c45 @ SCons1(x, _) = l
      val mc28 = if (n == BigInt(1)) {
        (SCons1[T](x, Val1[T](SNil1[T]())), BigInt(5))
      } else {
        val ir53 = n - BigInt(1)
        val ir21 = c45 match {
          case SCons1(_, Val1(x610)) =>
            (x610, BigInt(5))
          case SCons1(_, f345 @ Fun3(_)) =>
            val lr6 = lookup[Stream2[T]](List(6113, f345))
            val mc27 = if (lr6._1) {
              (lr6._2, BigInt(1))
            } else {
              val e222 = ValOrFun.gettime[T](f345)
              (update[Stream2[T]](List(6113, f345), e222._1), BigInt(3) + e222._2)
            }
            (mc27._1, BigInt(7) + mc27._2)
        }
        (SCons1[T](x, Fun3[T](() => {
          val e226 = takeLazytime[T](ir53, ir21._1)
          (e226._1, BigInt(1) + e226._2)
        })), BigInt(6) + ir21._2)
      }
      (mc28._1, BigInt(3) + mc28._2)
    }
    (bd14._1, bd14._2)
  }
  
  @invstate
  def revAppendtime[T](l1 : Stream2[T], l2 : Stream2[T]): (Stream2[T], BigInt) = {
    val bd10 = l1 match {
      case SNil1() =>
        (l2, BigInt(2))
      case c39 @ SCons1(x, _) =>
        val e189 = c39 match {
          case SCons1(_, Val1(x561)) =>
            (x561, BigInt(5))
          case SCons1(_, f337 @ Fun3(_)) =>
            val lr4 = lookup[Stream2[T]](List(6113, f337))
            val mc20 = if (lr4._1) {
              (lr4._2, BigInt(1))
            } else {
              val e188 = ValOrFun.gettime[T](f337)
              (update[Stream2[T]](List(6113, f337), e188._1), BigInt(3) + e188._2)
            }
            (mc20._1, BigInt(7) + mc20._2)
        }
        val e194 = revAppendtime[T](e189._1, SCons1[T](x, Val1[T](l2)))
        (e194._1, (BigInt(7) + e194._2) + e189._2)
    }
    (bd10._1, bd10._2)
  }
  
  @invstate
  def droptime[T](n : BigInt, l : Stream2[T]): (Stream2[T], BigInt) = {
    val bd9 = if (n == BigInt(0)) {
      (l, BigInt(2))
    } else {
      val el3 = l match {
        case SNil1() =>
          (l, BigInt(2))
        case c38 @ SCons1(x, _) =>
          val e183 = c38 match {
            case SCons1(_, Val1(x554)) =>
              (x554, BigInt(5))
            case SCons1(_, f335 @ Fun3(_)) =>
              val lr3 = lookup[Stream2[T]](List(6113, f335))
              val mc16 = if (lr3._1) {
                (lr3._2, BigInt(1))
              } else {
                val e182 = ValOrFun.gettime[T](f335)
                (update[Stream2[T]](List(6113, f335), e182._1), BigInt(3) + e182._2)
              }
              (mc16._1, BigInt(7) + mc16._2)
          }
          val e184 = droptime[T](n - BigInt(1), e183._1)
          (e184._1, (BigInt(6) + e184._2) + e183._2)
      }
      (el3._1, BigInt(2) + el3._2)
    }
    (bd9._1, bd9._2)
  }
  
  @invstate
  def taketime[T](n : BigInt, l : Stream2[T]): (Stream2[T], BigInt) = {
    val bd15 = if (n == BigInt(0)) {
      (SNil1[T](), BigInt(3))
    } else {
      val el5 = l match {
        case SNil1() =>
          (l, BigInt(2))
        case c48 @ SCons1(x, _) =>
          val e237 = c48 match {
            case SCons1(_, Val1(x618)) =>
              (x618, BigInt(5))
            case SCons1(_, f347 @ Fun3(_)) =>
              val lr7 = lookup[Stream2[T]](List(6113, f347))
              val mc31 = if (lr7._1) {
                (lr7._2, BigInt(1))
              } else {
                val e236 = ValOrFun.gettime[T](f347)
                (update[Stream2[T]](List(6113, f347), e236._1), BigInt(3) + e236._2)
              }
              (mc31._1, BigInt(7) + mc31._2)
          }
          val e238 = taketime[T](n - BigInt(1), e237._1)
          (SCons1[T](x, Val1[T](e238._1)), (BigInt(8) + e238._2) + e237._2)
      }
      (el5._1, BigInt(2) + el5._2)
    }
    (bd15._1, bd15._2)
  }
  
  @invstate
  def rotateRevtime[T](r : Stream2[T], f : Stream2[T], a : Stream2[T]): (Stream2[T], BigInt) = {
    val bd12 = r match {
      case SNil1() =>
        val e197 = revAppendtime[T](f, a)
        (e197._1, BigInt(3) + e197._2)
      case c41 @ SCons1(x, _) =>
        val ir17 = c41 match {
          case SCons1(_, Val1(x578)) =>
            (x578, BigInt(5))
          case SCons1(_, f340 @ Fun3(_)) =>
            val lr5 = lookup[Stream2[T]](List(6113, f340))
            val mc24 = if (lr5._1) {
              (lr5._2, BigInt(1))
            } else {
              val e199 = ValOrFun.gettime[T](f340)
              (update[Stream2[T]](List(6113, f340), e199._1), BigInt(3) + e199._2)
            }
            (mc24._1, BigInt(7) + mc24._2)
        }
        val e202 = droptime[T](BigInt(2), f)
        val e321 = e202._1
        val e205 = taketime[T](BigInt(2), f)
        val e208 = revAppendtime[T](e205._1, a)
        val e327 = e208._1
        (SCons1[T](x, Fun3[T](() => {
          val e213 = rotateRevtime[T](ir17._1, e321, e327)
          (e213._1, BigInt(1) + e213._2)
        })), (((BigInt(10) + e208._2) + e205._2) + e202._2) + ir17._2)
    }
    (bd12._1, bd12._2)
  }
  
  @invstate
  def rotateDroptime[T](r : Stream2[T], i : BigInt, f : Stream2[T]): (Stream2[T], BigInt) = {
    val c55 = BigInt(4)
    val bd6 = if (i < BigInt(2) || r == SNil1[T]()) {
      val e109 = droptime[T](i, f)
      val e112 = rotateRevtime[T](r, e109._1, SNil1[T]())
      (e112._1, ((BigInt(4) + c55) + e112._2) + e109._2)
    } else {
      val el2 = {
        val c32 @ SCons1(x, _) = r
        val ir12 = c32 match {
          case SCons1(_, Val1(x521)) =>
            (x521, BigInt(5))
          case SCons1(_, f303 @ Fun3(_)) =>
            val lr2 = lookup[Stream2[T]](List(6113, f303))
            val mc12 = if (lr2._1) {
              (lr2._2, BigInt(1))
            } else {
              val e114 = ValOrFun.gettime[T](f303)
              (update[Stream2[T]](List(6113, f303), e114._1), BigInt(3) + e114._2)
            }
            (mc12._1, BigInt(7) + mc12._2)
        }
        val ir24 = i - BigInt(2)
        val e119 = droptime[T](BigInt(2), f)
        val e293 = e119._1
        (SCons1[T](x, Fun3[T](() => {
          val e124 = rotateDroptime[T](ir12._1, ir24, e293)
          (e124._1, BigInt(1) + e124._2)
        })), (BigInt(8) + e119._2) + ir12._2)
      }
      (el2._1, (BigInt(1) + c55) + el2._2)
    }
    (bd6._1, bd6._2)
  }
  
  @invisibleBody
  def createQueuetime[T](f : Stream2[T], lenf : BigInt, sf : Stream2[T], r : Stream2[T], lenr : BigInt, sr : Stream2[T]): (Queue2[T], BigInt) = {
    val c57 = BigInt(3)
    val bd2 = if (lenf > BigInt(1) + BigInt(2) * lenr) {
      val ir32 = (lenf + lenr) / BigInt(2)
      val e33 = rotateDroptime[T](r, ir32, f)
      val e339 = e33._1
      val e36 = takeLazytime[T](ir32, f)
      val e341 = e36._1
      (Queue2[T](e341, ir32, e341, e339, (lenf + lenr) - ir32, e339), ((BigInt(8) + c57) + e36._2) + e33._2)
    } else {
      val c59 = BigInt(3)
      val el1 = if (lenr > BigInt(1) + BigInt(2) * lenf) {
        val ir40 = (lenf + lenr) / BigInt(2)
        val ir42 = (lenf + lenr) - ir40
        val e54 = rotateDroptime[T](f, ir42, r)
        val e351 = e54._1
        val e57 = takeLazytime[T](ir42, r)
        val e353 = e57._1
        (Queue2[T](e351, ir40, e351, e353, ir42, e353), ((BigInt(8) + c59) + e57._2) + e54._2)
      } else {
        (Queue2[T](f, lenf, sf, r, lenr, sr), BigInt(2) + c59)
      }
      (el1._1, (BigInt(1) + c57) + el1._2)
    }
    (bd2._1, bd2._2)
  }
  
  @invisibleBody
  def forcetime[T](tar : Stream2[T], htar : Stream2[T], other : Stream2[T], hother : Stream2[T]): (Stream2[T], BigInt) = {
    val bd = tar match {
      case c21 @ SCons1(_, _) =>
        val mc2 = c21 match {
          case SCons1(_, Val1(x458)) =>
            (x458, BigInt(5))
          case SCons1(_, f237 @ Fun3(_)) =>
            val lr = lookup[Stream2[T]](List(6113, f237))
            val mc1 = if (lr._1) {
              (lr._2, BigInt(1))
            } else {
              val e15 = ValOrFun.gettime[T](f237)
              (update[Stream2[T]](List(6113, f237), e15._1), BigInt(3) + e15._2)
            }
            (mc1._1, BigInt(7) + mc1._2)
        }
        (mc2._1, BigInt(2) + mc2._2)
      case _ =>
        (tar, BigInt(2))
    }
    (bd._1, bd._2)
  }
  
  def forceTwicetime[T](q : Queue2[T]): ((Stream2[T], Stream2[T]), BigInt) = {
    val e253 = forcetime[T](q.sf74, q.f226, q.r237, q.sr74)
    val e261 = forcetime[T](e253._1, q.f226, q.r237, q.sr74)
    val e416 = e261._1
    val e269 = forcetime[T](q.sr74, q.r237, q.f226, e416)
    val e276 = forcetime[T](e269._1, q.r237, q.f226, e416)
    ((e416, e276._1), (((BigInt(17) + e276._2) + e269._2) + e261._2) + e253._2)
  }
  
  def emptytime[T](): (Queue2[T], BigInt) = {
    val ir48 = SNil1[T]()
    (Queue2[T](ir48, BigInt(0), ir48, ir48, BigInt(0), ir48), BigInt(2))
  }
  
  def constime[T](x : T, q : Queue2[T]): (Queue2[T], BigInt) = {
    val e141 = forcetime[T](q.sf74, q.f226, q.r237, q.sr74)
    val e363 = e141._1
    val e149 = forcetime[T](q.sr74, q.r237, q.f226, e363)
    val e165 = createQueuetime[T](SCons1[T](x, Val1[T](q.f226)), BigInt(1) + q.lenf76, e363, q.r237, q.lenr76, e149._1)
    (e165._1, ((BigInt(17) + e165._2) + e149._2) + e141._2)
  }
  
  def tailtime[T](q : Queue2[T]): (Queue2[T], BigInt) = {
    val e244 = tailSubtime[T](q)
    (e244._1, BigInt(1) + e244._2)
  }
  
  def tailSubtime[T](q : Queue2[T]): (Queue2[T], BigInt) = {
    val bd3 = q.f226 match {
      case c28 @ SCons1(x, _) =>
        val e84 = forceTwicetime[T](q)
        val ir9 = {
          val (nsf, nsr) = e84._1
          ((nsf, nsr), BigInt(6) + e84._2)
        }
        val ir59 = ir9._1
        val e91 = c28 match {
          case SCons1(_, Val1(x497)) =>
            (x497, BigInt(5))
          case SCons1(_, f266 @ Fun3(_)) =>
            val lr1 = lookup[Stream2[T]](List(6113, f266))
            val mc6 = if (lr1._1) {
              (lr1._2, BigInt(1))
            } else {
              val e90 = ValOrFun.gettime[T](f266)
              (update[Stream2[T]](List(6113, f266), e90._1), BigInt(3) + e90._2)
            }
            (mc6._1, BigInt(7) + mc6._2)
        }
        val e102 = createQueuetime[T](e91._1, q.lenf76 - BigInt(1), ir59._1, q.r237, q.lenr76, ir59._2)
        (e102._1, ((BigInt(11) + e102._2) + e91._2) + ir9._2)
      case SNil1() =>
        val e103 = emptytime[T]
        (e103._1, BigInt(5) + e103._2)
    }
    (bd3._1, bd3._2)
  }
  
  def reversetime[T](q : Queue2[T]): (Queue2[T], BigInt) = (Queue2[T](q.r237, q.lenr76, q.sr74, q.f226, q.lenf76, q.sf74), BigInt(7))

  def snoc[T](x: T, q: Queue2[T]): Queue2[T] = {
    //require(q.valid)
    reversetime(constime(x, reversetime(q)._1)._1)._1
  }

//  def main(args: Array[String]): Unit = {
//    import scala.util.Random
//    val rand = Random
//
//    var points = (1 to 20).toList
//    points = points.map(x => 3*(1 << (x - 1)))
//    // var size = points.map(x => BigInt(x)).to[scalaList]
//    var size = points.map(x => (x)).toList
//
//    var ops = scalaList[BigInt]()
//    var orb = scalaList[BigInt]()
//    // points.foreach { length =>
//    //   var rtd = emptytime[BigInt]()._1
//    //   for (i <- 0 until length) {
//    //     rtd = snoc[BigInt](BigInt(0), rtd)
//    //   }
//    //   ops :+= {reversetime[BigInt](rtd)._2}
//    // }
//    // minresults(ops, scalaList(7), List("constant"), List(), size, "dequereverse")
//
//    // size = points.map(x => BigInt(x + 1)).to[scalaList]
//
//    ops = scalaList[BigInt]()
//    orb = scalaList[BigInt]()
//    points.foreach { length =>
//      var rtd = emptytime[BigInt]()._1
//      for (i <- 0 until (length + 1)) {
//        rtd = constime[BigInt](BigInt(0), rtd)._1
//      }
//      ops += {constime[BigInt](BigInt(0), rtd)._2}
//      orb += {580}
//    }
//    dumpdata(size, ops, orb, "dequecons", "orb")
//    // minresults(ops, scalaList(580), List("constant"), List(), size, "dequecons")
//
//    // ops = List[BigInt]()
//    // orb = List[BigInt]()
//    // points.foreach { length =>
//    //   var rtd = emptytime[BigInt]()._1
//    //   for (i <- 0 until (length + 1)) {
//    //     rtd = constime[BigInt](BigInt(0), rtd)._1
//    //   }
//    //   rtd = reversetime[BigInt](rtd)._1
//    //   ops :+= {tailtime[BigInt](rtd)._2}
//    //   orb :+= {970}
//    // }
//    // dumpdata(size, ops, orb, "dequetail", "orb")
//    // minresults(ops, scalaList(970), List("constant"), List(), size, "dequetail")
//
//  }
  
    /**
   * Benchmark specific parameters
   */
  abstract class RunContext {
    def coeffs: scalaList[BigInt] //from lower to higher-order terms
    def coeffNames = List("constant") // names of the coefficients
    val termsSize = 0 // number of terms (i.e monomials) in the template
    def getTermsForPoint(i: BigInt): scalaList[BigInt] = scalaList()
    def inputFromPoint(i: Int) = {
      val len = 3*(1 << (i - 1))
      var rtd = emptytime[BigInt]()._1
      for (i <- 0 until (len + 1)) {
        rtd = constime[BigInt](BigInt(0), rtd)._1
      }
      rtd
    }
    val dirname = "Deque"
    val filePrefix: String
    val points = (1 to 15)
    val concreteInstFun: Queue2[BigInt] => BigInt

  }
  object ConsContext extends RunContext {
    override def coeffs = scalaList[BigInt](580)
    override val filePrefix = "deq-cons" // the abbrevation used in the paper  
    override val concreteInstFun = (rtq: Queue2[BigInt]) => constime[BigInt](BigInt(0), rtq)._2
  }

  object TailContext extends RunContext {
    override def coeffs = scalaList[BigInt](970)
    override val filePrefix = "deq-tail" // the abbrevation used in the paper  
    override val concreteInstFun = (rtd: Queue2[BigInt]) => tailtime[BigInt](rtd)._2
  }
  val ctxts: scalaList[RunContext] = scalaList(ConsContext, TailContext)
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

object ValOrFun {
  def gettime[T](thiss : Deque.ValOrFun2[T]): (Deque.Stream2[T], BigInt) = {
    val bd4 = thiss match {
      case Deque.Fun3(f278) =>
        val e105 = f278()
        (e105._1, BigInt(4) + e105._2)
      case Deque.Val1(x502) =>
        (x502, BigInt(4))
    }
    (bd4._1, bd4._2)
  }
}

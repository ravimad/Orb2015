package allocAnalysis

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

  case class SCons1[T](x440 : T, next63 : ValOrFun2[T]) extends Stream2[T]

  case class SNil1[T]() extends Stream2[T]

  abstract class ValOrFun2[T]

  case class Val1[T](x438 : Stream2[T]) extends ValOrFun2[T]

  case class Fun3[T](fun23 : () => (Stream2[T], BigInt)) extends ValOrFun2[T]

  case class Queue2[T](f225 : Stream2[T], lenf76 : BigInt, sf74 : Stream2[T], r237 : Stream2[T], lenr76 : BigInt, sr74 : Stream2[T])

  @invstate
  def takeLazyalloc[T](n : BigInt, l : Stream2[T]): (Stream2[T], BigInt) = {
    val bd14 = {
      val c32 @ SCons1(x, _) = l
      val mc28 = if (n == BigInt(1)) {
        (SCons1[T](x, Val1[T](SNil1[T]())), BigInt(3))
      } else {
        val ir64 = n - BigInt(1)
        val ir21 = c32 match {
          case SCons1(_, Val1(x505)) =>
            (x505, BigInt(0))
          case SCons1(_, f297 @ Fun3(_)) =>
            val lr6 = lookup[Stream2[T]](List(6103, f297))
            val mc27 = if (lr6._1) {
              (lr6._2, BigInt(0))
            } else {
              val e222 = ValOrFun.getalloc[T](f297)
              (update[Stream2[T]](List(6103, f297), e222._1), BigInt(1) + e222._2)
            }
            (mc27._1, mc27._2)
        }
        (SCons1[T](x, Fun3[T](() => {
          val e226 = takeLazyalloc[T](ir64, ir21._1)
          (e226._1, e226._2)
        })), BigInt(3) + ir21._2)
      }
      (mc28._1, mc28._2)
    }
    (bd14._1, bd14._2)
  }

  @invstate
  def revAppendalloc[T](l1 : Stream2[T], l2 : Stream2[T]): (Stream2[T], BigInt) = {
    val bd10 = l1 match {
      case SNil1() =>
        (l2, BigInt(0))
      case c30 @ SCons1(x, _) =>
        val e189 = c30 match {
          case SCons1(_, Val1(x490)) =>
            (x490, BigInt(0))
          case SCons1(_, f295 @ Fun3(_)) =>
            val lr4 = lookup[Stream2[T]](List(6103, f295))
            val mc20 = if (lr4._1) {
              (lr4._2, BigInt(0))
            } else {
              val e188 = ValOrFun.getalloc[T](f295)
              (update[Stream2[T]](List(6103, f295), e188._1), BigInt(1) + e188._2)
            }
            (mc20._1, mc20._2)
        }
        val e194 = revAppendalloc[T](e189._1, SCons1[T](x, Val1[T](l2)))
        (e194._1, (BigInt(2) + e194._2) + e189._2)
    }
    (bd10._1, bd10._2)
  }

  @invstate
  def dropalloc[T](n : BigInt, l : Stream2[T]): (Stream2[T], BigInt) = {
    val bd9 = if (n == BigInt(0)) {
      (l, BigInt(0))
    } else {
      val el3 = l match {
        case SNil1() =>
          (l, BigInt(0))
        case c29 @ SCons1(x, _) =>
          val e183 = c29 match {
            case SCons1(_, Val1(x485)) =>
              (x485, BigInt(0))
            case SCons1(_, f294 @ Fun3(_)) =>
              val lr3 = lookup[Stream2[T]](List(6103, f294))
              val mc16 = if (lr3._1) {
                (lr3._2, BigInt(0))
              } else {
                val e182 = ValOrFun.getalloc[T](f294)
                (update[Stream2[T]](List(6103, f294), e182._1), BigInt(1) + e182._2)
              }
              (mc16._1, mc16._2)
          }
          val e184 = dropalloc[T](n - BigInt(1), e183._1)
          (e184._1, e184._2 + e183._2)
      }
      (el3._1, el3._2)
    }
    (bd9._1, bd9._2)
  }

  @invstate
  def takealloc[T](n : BigInt, l : Stream2[T]): (Stream2[T], BigInt) = {
    val bd15 = if (n == BigInt(0)) {
      (SNil1[T](), BigInt(1))
    } else {
      val el5 = l match {
        case SNil1() =>
          (l, BigInt(0))
        case c35 @ SCons1(x, _) =>
          val e237 = c35 match {
            case SCons1(_, Val1(x511)) =>
              (x511, BigInt(0))
            case SCons1(_, f298 @ Fun3(_)) =>
              val lr7 = lookup[Stream2[T]](List(6103, f298))
              val mc31 = if (lr7._1) {
                (lr7._2, BigInt(0))
              } else {
                val e236 = ValOrFun.getalloc[T](f298)
                (update[Stream2[T]](List(6103, f298), e236._1), BigInt(1) + e236._2)
              }
              (mc31._1, mc31._2)
          }
          val e238 = takealloc[T](n - BigInt(1), e237._1)
          (SCons1[T](x, Val1[T](e238._1)), (BigInt(2) + e238._2) + e237._2)
      }
      (el5._1, el5._2)
    }
    (bd15._1, bd15._2)
  }

  @invstate
  def rotateRevalloc[T](r : Stream2[T], f : Stream2[T], a : Stream2[T]): (Stream2[T], BigInt) = {
    val bd12 = r match {
      case SNil1() =>
        val e197 = revAppendalloc[T](f, a)
        (e197._1, e197._2)
      case c31 @ SCons1(x, _) =>
        val ir17 = c31 match {
          case SCons1(_, Val1(x497)) =>
            (x497, BigInt(0))
          case SCons1(_, f296 @ Fun3(_)) =>
            val lr5 = lookup[Stream2[T]](List(6103, f296))
            val mc24 = if (lr5._1) {
              (lr5._2, BigInt(0))
            } else {
              val e199 = ValOrFun.getalloc[T](f296)
              (update[Stream2[T]](List(6103, f296), e199._1), BigInt(1) + e199._2)
            }
            (mc24._1, mc24._2)
        }
        val e202 = dropalloc[T](BigInt(2), f)
        val e401 = e202._1
        val e205 = takealloc[T](BigInt(2), f)
        val e208 = revAppendalloc[T](e205._1, a)
        val e407 = e208._1
        (SCons1[T](x, Fun3[T](() => {
          val e213 = rotateRevalloc[T](ir17._1, e401, e407)
          (e213._1, e213._2)
        })), (((BigInt(3) + e208._2) + e205._2) + e202._2) + ir17._2)
    }
    (bd12._1, bd12._2)
  }

  @invstate
  def rotateDropalloc[T](r : Stream2[T], i : BigInt, f : Stream2[T]): (Stream2[T], BigInt) = {
    val bd6 = if (i < BigInt(2) || r == SNil1[T]()) {
      val e109 = dropalloc[T](i, f)
      val e112 = rotateRevalloc[T](r, e109._1, SNil1[T]())
      (e112._1, (BigInt(2) + e112._2) + e109._2)
    } else {
      val el2 = {
        val c26 @ SCons1(x, _) = r
        val ir12 = c26 match {
          case SCons1(_, Val1(x470)) =>
            (x470, BigInt(0))
          case SCons1(_, f271 @ Fun3(_)) =>
            val lr2 = lookup[Stream2[T]](List(6103, f271))
            val mc12 = if (lr2._1) {
              (lr2._2, BigInt(0))
            } else {
              val e114 = ValOrFun.getalloc[T](f271)
              (update[Stream2[T]](List(6103, f271), e114._1), BigInt(1) + e114._2)
            }
            (mc12._1, mc12._2)
        }
        val ir44 = i - BigInt(2)
        val e119 = dropalloc[T](BigInt(2), f)
        val e359 = e119._1
        (SCons1[T](x, Fun3[T](() => {
          val e124 = rotateDropalloc[T](ir12._1, ir44, e359)
          (e124._1, e124._2)
        })), (BigInt(3) + e119._2) + ir12._2)
      }
      (el2._1, BigInt(1) + el2._2)
    }
    (bd6._1, bd6._2)
  }

  @invisibleBody
  def createQueuealloc[T](f : Stream2[T], lenf : BigInt, sf : Stream2[T], r : Stream2[T], lenr : BigInt, sr : Stream2[T]): (Queue2[T], BigInt) = {
    val bd2 = if (lenf > BigInt(1) + BigInt(2) * lenr) {
      val ir24 = (lenf + lenr) / BigInt(2)
      val e33 = rotateDropalloc[T](r, ir24, f)
      val e291 = e33._1
      val e36 = takeLazyalloc[T](ir24, f)
      val e293 = e36._1
      (Queue2[T](e293, ir24, e293, e291, (lenf + lenr) - ir24, e291), (BigInt(1) + e36._2) + e33._2)
    } else {
      val el1 = if (lenr > BigInt(1) + BigInt(2) * lenf) {
        val ir32 = (lenf + lenr) / BigInt(2)
        val ir34 = (lenf + lenr) - ir32
        val e54 = rotateDropalloc[T](f, ir34, r)
        val e303 = e54._1
        val e57 = takeLazyalloc[T](ir34, r)
        val e305 = e57._1
        (Queue2[T](e303, ir32, e303, e305, ir34, e305), (BigInt(1) + e57._2) + e54._2)
      } else {
        (Queue2[T](f, lenf, sf, r, lenr, sr), BigInt(1))
      }
      (el1._1, el1._2)
    }
    (bd2._1, bd2._2)
  }

  @invisibleBody
  def forcealloc[T](tar : Stream2[T], htar : Stream2[T], other : Stream2[T], hother : Stream2[T]): (Stream2[T], BigInt) = {
    val bd = tar match {
      case c21 @ SCons1(_, _) =>
        val mc2 = c21 match {
          case SCons1(_, Val1(x456)) =>
            (x456, BigInt(0))
          case SCons1(_, f236 @ Fun3(_)) =>
            val lr = lookup[Stream2[T]](List(6103, f236))
            val mc1 = if (lr._1) {
              (lr._2, BigInt(0))
            } else {
              val e15 = ValOrFun.getalloc[T](f236)
              (update[Stream2[T]](List(6103, f236), e15._1), BigInt(1) + e15._2)
            }
            (mc1._1, mc1._2)
        }
        (mc2._1, mc2._2)
      case _ =>
        (tar, BigInt(0))
    }
    (bd._1, bd._2)
  }

  @invisibleBody
  def forceTwicealloc[T](q : Queue2[T]): ((Stream2[T], Stream2[T]), BigInt) = {
    val e253 = forcealloc[T](q.sf74, q.f225, q.r237, q.sr74)
    val e261 = forcealloc[T](e253._1, q.f225, q.r237, q.sr74)
    val e325 = e261._1
    val e269 = forcealloc[T](q.sr74, q.r237, q.f225, e325)
    val e276 = forcealloc[T](e269._1, q.r237, q.f225, e325)
    ((e325, e276._1), ((e276._2 + e269._2) + e261._2) + e253._2)
  }

  def emptyalloc[T](): (Queue2[T], BigInt) = {
    val ir66 = SNil1[T]()
    (Queue2[T](ir66, BigInt(0), ir66, ir66, BigInt(0), ir66), BigInt(2))
  }

  def consalloc[T](x : T, q : Queue2[T]): (Queue2[T], BigInt) = {
    val e141 = forcealloc[T](q.sf74, q.f225, q.r237, q.sr74)
    val e419 = e141._1
    val e149 = forcealloc[T](q.sr74, q.r237, q.f225, e419)
    val e165 = createQueuealloc[T](SCons1[T](x, Val1[T](q.f225)), BigInt(1) + q.lenf76, e419, q.r237, q.lenr76, e149._1)
    (e165._1, ((BigInt(2) + e165._2) + e149._2) + e141._2)
  }

  def tailalloc[T](q : Queue2[T]): (Queue2[T], BigInt) = {
    val e244 = tailSuballoc[T](q)
    (e244._1, e244._2)
  }

  def tailSuballoc[T](q : Queue2[T]): (Queue2[T], BigInt) = {
    val bd3 = q.f225 match {
      case c24 @ SCons1(x, _) =>
        val e84 = forceTwicealloc[T](q)
        val ir9 = {
          val (nsf, nsr) = e84._1
          ((nsf, nsr), e84._2)
        }
        val ir48 = ir9._1
        val e91 = c24 match {
          case SCons1(_, Val1(x461)) =>
            (x461, BigInt(0))
          case SCons1(_, f244 @ Fun3(_)) =>
            val lr1 = lookup[Stream2[T]](List(6103, f244))
            val mc6 = if (lr1._1) {
              (lr1._2, BigInt(0))
            } else {
              val e90 = ValOrFun.getalloc[T](f244)
              (update[Stream2[T]](List(6103, f244), e90._1), BigInt(1) + e90._2)
            }
            (mc6._1, mc6._2)
        }
        val e102 = createQueuealloc[T](e91._1, q.lenf76 - BigInt(1), ir48._1, q.r237, q.lenr76, ir48._2)
        (e102._1, (e102._2 + e91._2) + ir9._2)
      case SNil1() =>
        val e103 = emptyalloc[T]
        (e103._1, e103._2)
    }
    (bd3._1, bd3._2)
  }

  def reversealloc[T](q : Queue2[T]): (Queue2[T], BigInt) = (Queue2[T](q.r237, q.lenr76, q.sr74, q.f225, q.lenf76, q.sf74), BigInt(1))

  def snoc[T](x: T, q: Queue2[T]): Queue2[T] = {
    //require(q.valid)
    reversealloc(consalloc(x, reversealloc(q)._1)._1)._1
  }

  // def main(args: Array[String]): Unit = {
  //   import scala.util.Random
  //   val rand = Random

  //   val points = (0 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
  //   var size = points.map(x => BigInt(x)).to[scalaList]
  //   var size2 = points.map(x => (x)).toList

  //   var ops = List[BigInt]()
  //   var orb = List[BigInt]()
  //   points.foreach { length =>
  //     var rtd = emptyalloc[BigInt]()._1
  //     for (i <- 0 until length) {
  //       rtd = snoc[BigInt](BigInt(0), rtd)
  //     }
  //     ops :+= {reversealloc[BigInt](rtd)._2}
  //     orb :+= {1}
  //   }
  //   dumpdata(size2, ops, orb, "dequereverse", "orb")
  //   minresults(ops, scalaList(1), List("constant"), List(), size, "dequereverse")

  //   size = points.map(x => BigInt(x + 1)).to[scalaList]

  //   ops = List[BigInt]()
  //   orb = List[BigInt]()
  //   points.foreach { length =>
  //     var rtd = emptyalloc[BigInt]()._1
  //     for (i <- 0 until (length + 1)) {
  //       rtd = consalloc[BigInt](BigInt(0), rtd)._1
  //     }
  //     ops :+= {consalloc[BigInt](BigInt(0), rtd)._2}
  //     orb :+= {50}
  //   }
  //   dumpdata(size2, ops, orb, "dequecons", "orb")
  //   minresults(ops, scalaList(50), List("constant"), List(), size, "dequecons")

  //   ops = List[BigInt]()
  //   orb = List[BigInt]()
  //   points.foreach { length =>
  //     var rtd = emptyalloc[BigInt]()._1
  //     for (i <- 0 until (length + 1)) {
  //       rtd = consalloc[BigInt](BigInt(0), rtd)._1
  //     }
  //     rtd = reversealloc[BigInt](rtd)._1
  //     ops :+= {tailalloc[BigInt](rtd)._2}
  //     orb :+= {78}
  //   }
  //   dumpdata(size2, ops, orb, "dequetail", "orb")
  //   minresults(ops, scalaList(78), List("constant"), List(), size, "dequetail")
  // }

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
      var rtd = emptyalloc[BigInt]()._1
      for (i <- 0 until (len + 1)) {
        rtd = consalloc[BigInt](BigInt(0), rtd)._1
      }
      rtd
    }
    val dirname = "alloc/Deque"
    val filePrefix: String
    val points = (1 to 20)
    val concreteInstFun: Queue2[BigInt] => BigInt

  }
  object ConsContext extends RunContext {
    override def coeffs = scalaList[BigInt](50)
    override val filePrefix = "deq-cons" // the abbrevation used in the paper
    override val concreteInstFun = (rtq: Queue2[BigInt]) => consalloc[BigInt](BigInt(0), rtq)._2
  }

  object ReverseContext extends RunContext {
    override def coeffs = scalaList[BigInt](1)
    override val filePrefix = "deq-reverse" // the abbrevation used in the paper
    override val concreteInstFun = (rtd: Queue2[BigInt]) => reversealloc[BigInt](rtd)._2
  }

  object TailContext extends RunContext {
    override def coeffs = scalaList[BigInt](78)
    override val filePrefix = "deq-tail" // the abbrevation used in the paper
    override val concreteInstFun = (rtd: Queue2[BigInt]) => tailalloc[BigInt](rtd)._2
  }
  val ctxts: scalaList[RunContext] = scalaList(ConsContext, ReverseContext, TailContext)
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
  def getalloc[T](thiss : Deque.ValOrFun2[T]): (Deque.Stream2[T], BigInt) = {
    val bd4 = thiss match {
      case Deque.Fun3(f249) =>
        val e105 = f249()
        (e105._1, e105._2)
      case Deque.Val1(x464) =>
        (x464, BigInt(0))
    }
    (bd4._1, bd4._2)
  }
}

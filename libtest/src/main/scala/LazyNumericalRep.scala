package lrpTIMERUN

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._
import leon.collection._
import collection._

/**
 * This benchmark requires an unrollfactor of 5
 */

object DigitObject {
  sealed abstract class Digit
  case class Zero() extends Digit {
    @ignore
    override def toString = "0"
  }
  case class One() extends Digit {
    @ignore
    override def toString = "1"
  }
}

import DigitObject._
object LazyNumericalRep {

  @finite
  sealed abstract class NumList
  case class Tip() extends NumList
  case class Spine(head: Digit, rear: NumStream) extends NumList

  sealed abstract class NumStream {

    @inline
    def isSusp = this match {
      case _: Susp => true
      case _       => false
    }

    lazy val fval = {
      require(isSusp)
      this match {
        case Susp(f) => f()
      }
    }

    def get: NumList = {
      this match {
        case Susp(f) => fval
        case Val(x)  => x
      }
    }

    def getV = this match {
      case Susp(f) => fval*
      case Val(x)  => x
    }

    def isCached = this match {
      case _: Val => true
      case _      => fval.cached
    }
  }
  private case class Val(x: NumList) extends NumStream
  private case class Susp(fun: () => NumList) extends NumStream



  /**
   * (a) If we push a carry and get back 0 then there is a new carry
   * (b) If we push a carry and get back 1 then there the carry has been fully pushed
   * Note that if 'q' has a suspension then it would have a carry.
   */
  @invisibleBody
  def pushUntilCarry(q: NumStream): NumStream = {
    q.getV match {
      case Spine(Zero(), rear) => // if we push a carry and get back 0 then there is a new carry
        pushUntilCarry(rear)
      case Spine(_, rear) => // if we push a carry and get back 1 then there the carry has been fully pushed
        rear
      case Tip() => q
    }
  }

  case class Number(digs: NumStream, schedule: List[NumStream]) 

  def emptyNum = Number(Val(Tip()), Nil())

  @invisibleBody
  def inc(xs: NumStream): NumList = {
    xs.get match {
      case Tip() =>
        Spine(One(), xs)
      case s @ Spine(Zero(), rear) =>
        Spine(One(), rear)
      case s @ Spine(_, _) =>
        incLazy(xs)
    }
  } 

  @invisibleBody
  @invstate
  def incLazy(xs: NumStream): NumList = {
    xs.get match {
      case Spine(head, rear) => // here, rear is guaranteed to be evaluated by 'zeroPrecedeLazy' invariant
        val carry = One()
        rear.get match {
          case Tip() =>
            Spine(Zero(), Val(Spine(carry, rear)))

          case Spine(Zero(), srearfun) =>
            Spine(Zero(), Val(Spine(carry, srearfun)))

          case s =>
            Spine(Zero(), Susp(() => incLazy(rear)))
        }
    }
  } 

  @invisibleBody
  def incNum(w: Number): (NumStream, List[NumStream]) = {
    val nq = inc(w.digs)
    val nsched = nq match {
      case Spine(Zero(), rear: Susp) =>
        Cons(rear, w.schedule) // this is the only case where we create a new lazy closure
      case _ =>
        w.schedule
    }
    (Val(nq), nsched)
  } 

  @invisibleBody
  def Pay[T](q: NumStream, scheds: List[NumStream]): List[NumStream] = {
    scheds match {
      case c @ Cons(head, rest) =>
        head.get match {
          case Spine(Zero(), rear: Susp) => Cons(rear, rest)
          case _                         => rest
        }
      case Nil() => scheds
    }
  } 

  /**
   * Pushing an element to the left of the queue preserves the data-structure invariants
   */
  @invisibleBody
  def incAndPay(w: Number) = {
    val (q, scheds) = incNum(w)
    val nscheds = Pay(q, scheds)
    Number(q, nscheds)

  } 

  def firstDigit(w: Number): Digit = {
    w.digs.get match {
      case Spine(d, _) => d
    }
  }

  def suffix[T](q: NumStream, suf: NumStream): Boolean = {
    if (q == suf) true
    else {
      q.getV match {
        case Spine(_, rear) =>
          suffix(rear, suf)
        case Tip() => false
      }
    }
  }

  def properSuffix[T](l: NumStream, suf: NumStream): Boolean = {
    l.getV match {
      case Spine(_, rear) =>
        suffix(rear, suf)
      case _ => false
    }
  } 

  @ignore
  def main(args: Array[String]) {
    //import eagerEval.BigNums
    import scala.util.Random
    import scala.math.BigInt
    import stats._
    import collection._
    import scala.util.Random
    import java.lang.management._
    import scala.collection.JavaConversions._
    
    val rand = Random

    val points = (3 to 20)
    val size = points.map(x => ((1 << x) - 1)).toList

    val nooftimes = (1 to 10000000)
    val length = ((1 << 20) - 1)
    var totalTime = 0L
    var lazynum = emptyNum
    for (i <- 0 until length) {
      lazynum = incAndPay(lazynum)
    }

    nooftimes.foreach { _ =>  
      var t1 = System.nanoTime()
      var gct1 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
      val r = incAndPay(lazynum)
      var gct2 = ManagementFactory.getGarbageCollectorMXBeans().map(_.getCollectionTime()).sum
      totalTime += (System.nanoTime() - t1) - (gct2 - gct1)
    }
    println(s"${totalTime/1000000000.0} s")
  }
}

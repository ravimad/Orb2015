package lazybenchmarks

import leon.lazyeval._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.lazyeval.$._
import leon.collection._

/**
 * This benchmark is very for finding counter-examples
 */
object Esop15Benchmarks {
  
  /**
   * A stream of integers (the tail is lazy)
   */
  sealed abstract class IStream {
    /*def size: BigInt = {
      this match {
        case SCons(_, xs) => 1 + ssize(xs)
        case _            => BigInt(0)
      }
    } ensuring (_ >= 0)*/
  }
  case class SCons(x: BigInt, tail: $[IStream]) extends IStream
  case class SNil() extends IStream
  //def ssize(l: $[IStream]): BigInt = (l*).size
  
  /**
   * To be replaced by generic streams, when we support generics fully
   */
  sealed abstract class StreamPairs  
  case class PCons(pair: (BigInt, BigInt), tail: $[StreamPairs]) extends StreamPairs
  case class PNil() extends StreamPairs  
  
  def zipWith(xs: $[IStream], ys: $[IStream]): StreamPairs = {
    (xs.value, ys.value) match {
      case (SCons(x, xtail), SCons(y, ytail)) =>
        PCons((x, y), $(zipWith(xtail, ytail)))
      case _ => 
        PNil()
    }
  } ensuring(_ => time <= 65)

  def nextFib(x: BigInt, y: BigInt, n: BigInt): IStream = {
    if (n <= 0)
      SNil()
    else {
      val next = x + y
      SCons(next, $(nextFib(y, next, n - 1)))
    }
  } ensuring(_ => time <= 20)
  
  def fibStream(n: BigInt) : IStream = {
    SCons(0, SCons(1, $(nextFib(0, 1, n))))
  }

  def nthFib(n: BigInt, fs: $[IStream]): BigInt = {
    require(n >= 0)
    fs.value match {
      case SCons(x, tail) =>
        if (n == 0)
          x
        else
          nthFib(n - 1, tail)
      case SNil() => BigInt(-1)
    }
  } ensuring(_ => time <= 40 * n + 40) // you get a counter-example for 20*n + 20
}
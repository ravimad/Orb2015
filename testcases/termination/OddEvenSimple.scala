/* Copyright 2009-2016 EPFL, Lausanne */
import leon.lang._
import leon.math._

object Test {

  def isOdd(n: BigInt): Boolean = {
    decreases(abs(n))
    require(n >= 0)
    if(n == 0) false
    else isEven(n-1)
  }

  def isEven(n: BigInt): Boolean = {
    decreases(abs(n))
    require(n >= 0)
    if(n == 0) true
    else isOdd(n-1)
  }

}
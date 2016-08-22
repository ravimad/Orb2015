/* Copyright 2009-2016 EPFL, Lausanne */
import leon.lang._
object OddEvenComplex {

  def rank(n: BigInt): BigInt = {
    if(n < 0) -2*n
    else n
  }

  def isOdd(n: BigInt): Boolean = {
    decreases(rank(n))
    if(n < 0) isOdd(-n)
    else if(n == 0) false
    else isEven(n-1)
  }

  def isEven(n: BigInt): Boolean = {
    decreases(rank(n))
    if(n < 0) isEven(-n)
    else if(n == 0) true
    else isOdd(n-1)
  }

}
import leon._
import lang._
import invariant._
import annotation._
import instrumentation._

object GCD {
  import Arithmetic._ 
  
  def gcd(x:BigInt, y: BigInt): BigInt = {
    require(x >= y && y >= 1 && modLogProp(x, y))
    val m = x % y
    if(m == 0) y
    else {
      gcd(y, m)
    }
  } ensuring(res => steps <= ? * log(x + y) + ?)
}


/**
 * Remove @library annotation and verify the properties with Leon.
 * With Orb, it exposes a transient bug.
 */
object Arithmetic {

  /**
   * Computes floor(log(x)) for the base 3/4 for all x >= 1
   */
  def log(x: BigInt): BigInt = {
    require(x >= 1)
    if (x <= 1) BigInt(0)
    else 1 + log(3*x / 4)
  } ensuring (_ >= 0)
  
  def logMonotone(x: BigInt, y: BigInt): Boolean = {
    require(x >= y && y >= 1)
    (if(y <= 1) true else logMonotone(3*x/4, 3*y/4))  && 
      (log(x) >= log(y)) 
  } holds
  
  /**
   * (3*(x+y)) / 4 >= y + x % y
   */
  @library
  def modProp(x: BigInt, y: BigInt): Boolean = {
     require(x >= y && y >= 1)      
     3*(x+y) / 4 >= y + (x % y)
  } holds
  
  def modLogProp(x: BigInt, y: BigInt): Boolean = {
     require(x >= y && y >= 1)
     val s = y + (x % y)
     val b = 3*(x+y) / 4
      modProp(x, y) && b >= s && logMonotone(b, s) && 
        log(x + y) >= log(s) + 1
  } holds
}


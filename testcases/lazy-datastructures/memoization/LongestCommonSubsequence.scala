import leon._
import mem._
import lang._
import annotation._
import instrumentation._
//import leon.invariant._

object LCS {
  def max(a: BigInt, b: BigInt): BigInt = {
    require(a >= 0 && b >= 0)
    if (a > b) a else b
  }

  @memoize
  def lcs(m: BigInt, n: BigInt, X: String, Y: String): BigInt = {
    require(n >= 0 && m >= 0)
    if(m == 0 || n == 0)
      BigInt(0)
    else if(X(m.toInt - 1) == Y(n.toInt - 1))
      1 + lcs(m - 1, n - 1, X, Y)
    else
      max(lcs(m - 1, n, X, Y), lcs(m, n - 1, X, Y))
  } ensuring(_ =>
    (m == 0 || n == 0 || (lcs(m - 1, n - 1, X, Y).isCached &&
      lcs(m - 1, n, X, Y).isCached && lcs(m, n - 1, X, Y).isCached)) &&
      time <= ?*m*n + ?*m + ?*n + ?)
}

import leon.lang._
import leon.math._

object Ackermann {
  def ackermann(m: BigInt, n: BigInt): BigInt = {
    decreases((abs(m), abs(n))) // a lexicographic ranking function
    require(m >= 0 && n >= 0)
    if (m == 0) n + 1
    else if (n == 0) ackermann(m - 1, 1)
    else ackermann(m - 1, ackermann(m, n - 1))
  }
}

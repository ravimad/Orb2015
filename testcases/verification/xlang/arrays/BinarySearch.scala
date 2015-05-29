import leon.lang._

/* VSTTE 2008 - Dafny paper */

object BinarySearch {

  def binarySearch(a: Array[BigInt], key: BigInt): Int = ({
    require(a.length > 0 && sorted(a, 0, a.length - 1))
    var low = 0
    var high = a.length - 1
    var res = -1

    (while(low <= high && res == -1) {
      val i = (high + low) / 2
      val v = a(i)

      if(v == key)
        res = i

      if(v > key)
        high = i - 1
      else if(v < key)
        low = i + 1
    }) invariant(
        res >= -1 &&
        res < a.length &&
        0 <= low && 
        low <= high + 1 && 
        high >= -1 &&
        high < a.length && 
        (if (res >= 0) 
            a(res) == key else 
            (!occurs(a, 0, low, key) && !occurs(a, high + 1, a.length, key))
        )
       )
    res
  }) ensuring(res => 
      res >= -1 && 
      res < a.length && 
      (if(res >= 0) a(res) == key else !occurs(a, 0, a.length, key)))


  def occurs(a: Array[BigInt], from: Int, to: Int, key: BigInt): Boolean = {
    require(a.length >= 0 && to <= a.length && from >= 0)
    arrayExists(a, from, to, (el: BigInt) => el == key)
  }

  def sorted(a: Array[BigInt], l: Int, u: Int): Boolean = {
    require(a.length > 0 && l >= 0 && u < a.length && l <= u)
    boundedForall(l, u, (i: Int) => a(i) <= a(i+1))
  }
}

package leon

/** Various utilities used throughout the Leon system */
package object utils {

  /** compute the fixpoint of a function.
    *
    * Apply the input function on an expression as long as until 
    * it stays the same (value equality) or until a set limit.
    *
    * @param f
    * @param limit
    * @param e
    * @return
    */
  def fixpoint[T](f: T => T, limit: Int = -1)(e: T): T = {
    var v1 = e
    var v2 = f(v1)
    var lim = limit
    while(v2 != v1 && lim != 0) {
      v1 = v2
      lim -= 1
      v2 = f(v2)
    }
    v2
  }
  
}

package withOrb

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._
import collection._

/**
 * Implementation of the Viterbi algorithm 
 * Wiki - https://en.wikipedia.org/wiki/Viterbi_algorithm
 * The probabilities are in logarithms.
 */
object Viterbi {

  @ignore
  var xstring = Array[BigInt]()
  @ignore
  var ystring = Array[BigInt]()
  /**
   * Observation space, O
   */
  @extern
  def O(i: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => time <= 1)
  /**
   * State space, S
   */
  @extern
  def S(i: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => time <= 1)
  /** 
   * Let K be the size of the state space. Then the transition matrix
   * A of size K * K such that A_{ij} stores the transition probability 
   * of transiting from state s_i to state s_j
   */
  @extern
  def A(i: BigInt, j: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => time <= 1)
  /**
   * Let N be the size of the observation space. Emission matrix B of 
   * size K * N such that B_{ij} stores the probability of observing o_j 
   * from state s_i
   */
  @extern
  def B(i: BigInt, j: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => time <= 1)
  /**
   * An array of initial probabilities C of size K such that C_i stores 
   * the probability that x_1 == s_i 
   */
  @extern
  def C(i: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => time <= 1)
  /**
   * Generated observations, Y
   */
  @extern
  def Y(i: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => time <= 1)

  // deps and it's lemmas
  def deps(j: BigInt, K: BigInt): Boolean = {
    require(j >= 0 && K >= 0)
    if(j <= 0) true
    else viterbiCached(0, j - 1, K) && deps(j - 1, K)
  }

  def viterbiCached(l: BigInt, j: BigInt, K: BigInt): Boolean = {
    require(l >= 0 && j >= 0 && K >= l)
    viterbi(l, j, K).cached && {
    if(l == K) true
    else viterbiCached(l + 1, j, K)} 
  }

  @traceInduct
  def depsMono(j: BigInt, K: BigInt, st1: Set[Fun[BigInt]], st2: Set[Fun[BigInt]]) = {
    require(j >= 0 && K >= 0)
    (st1.subsetOf(st2) && (deps(j, K) withState st1)) ==> (deps(j, K) withState st2)
  } holds

  def cachedLem(l: BigInt, j: BigInt, K: BigInt): Boolean = {
    require(j >= 0 && l >= 0 && K >= l)
    (if(l == 0) true
      else if(l == K) cachedLem(l - 1, j, K)
      else cachedLem(l + 1, j, K) && cachedLem(l - 1, j, K)
      ) && (viterbiCached(0, j, K) ==> viterbiCached(l, j, K))    
  } holds

  @invstate
  def fillEntry(l: BigInt, i: BigInt, j: BigInt, K: BigInt): BigInt = {
    require(i >= 0 && j >= 1 && l >= 0 && K >= l && K >= i && deps(j, K) && cachedLem(l, j - 1, K))
    val a1 = viterbi(l, j - 1, K) + A(l, i) + B(i, Y(j))
    if(l == K) a1
    else {
      val a2 = fillEntry(l + 1, i, j, K)
      if(a1 > a2) a1 else a2
    }
  } ensuring(time <= ? * (K - l) + ?)

  @invstate
  @memoize
  def viterbi(i: BigInt, j: BigInt, K: BigInt): BigInt = {
    require(i >= 0 && j >= 0 && K >= i && (j == 0 || j > 0 && deps(j, K)))
    if(j == 0) {
      C(i) + B(i, Y(0))
    } else {
      fillEntry(0, i, j, K)
    }
  } ensuring(time <= ? * K + ?)

  def fillColumn(i: BigInt, j: BigInt, K: BigInt): BigInt = {
    require(i >= 0 && j >= 0 && K >= i && (j == 0 || j > 0 && deps(j, K)))
    val v = viterbi(i, j, K)
    if(i != K) fillColumn(i + 1, j, K) else BigInt(0)
  } ensuring(res => {
    val in = inState[BigInt]
    val out = outState[BigInt]
      (j == 0 || depsMono(j, K, in, out)) && time <= ? * ((K - i) * K) + ?
  })

  // def fillTable(j: BigInt, T: BigInt, K: BigInt): BigInt = {
  //   require(j >= 0 && T >= j + 1 && K >= 1 && (j == 0 || j > 0 && deps(K - 1, j - 1, K))) //cachedLem(K - 1, j - , K - 1, T - 1, K) )
  //   val s = fillColumn(0, j, K)
  //   if(j != T - 1) fillTable(j + 1, T, K) else BigInt(0)
  // } ensuring(deps(K - 1, j, K) && time <= ? *((K * K) * (T - j)) + ?)

  // def viterbiSols(T: BigInt, K: BigInt): BigInt = {
  //   require(T >= 1 && K >= 1)
  //   fillTable(0, T, K)
  // } ensuring(time <= ? * ((K * K) * T) + ?)

}

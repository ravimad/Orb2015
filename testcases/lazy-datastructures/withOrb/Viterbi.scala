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
  def deps(i: BigInt, j: BigInt, K: BigInt): Boolean = {
    require(i >= 0 && j >= 0 && K >= i + 1)
    viterbi(i, j, K).cached &&
      (if (i <= 0 && j <= 0) true
      else if (i <= 0) deps(i, j - 1, K)
      else if (j <= 0) deps(i - 1, j, K)
      else deps(i - 1, j, K) && deps(i, j - 1, K))
  }

  @invisibleBody
  @traceInduct
  def depsMono(i: BigInt, j: BigInt, K: BigInt, st1: Set[Fun[BigInt]], st2: Set[Fun[BigInt]]) = {
    require(i >= 0 && j >= 0 && K >= i + 1)
    (st1.subsetOf(st2) && (deps(i, j, K) withState st1)) ==> (deps(i, j, K) withState st2)
  } holds

  @traceInduct
  def depsLem(i: BigInt, j: BigInt, m: BigInt, n: BigInt) = {
    require(i >= 0 && j >= 0 && m >= 0 && n >= 0)
    (i <= m && j <= n && deps(m, n)) ==> deps(i, j)
  } holds

  def fillEntry(l: BigInt, i: BigInt, j: BigInt, K: BigInt): BigInt = {
    require(i >= 0 && j >= 1 && l >= 0 && K >= l && K >= i + 1 && deps(K - 1, j - 1, K))
    if(l == K) BigInt(0)
    else {
      val a2 = fillEntry(l + 1, i, j, K)
      val a1 = viterbi(l, j - 1, K) + A(l, i) + B(i, Y(j))
      if(a1 > a2) a1 else a2
    }
  } ensuring(time <= ? * (K - l) + ?)

  @invstate
  @memoize
  @invisibleBody
  def viterbi(i: BigInt, j: BigInt, K: BigInt): BigInt = {
    require(i >= 0 && j >= 0 && K >= i + 1 && (j == 0 || deps(K - 1, j - 1, K)))
    if(j == 0) {
      C(i) + B(i, Y(0))
    } else {
      fillEntry(0, i, j, K)
    }
  } ensuring(res => {
    val in = inState[BigInt]
    val out = outState[BigInt]
      (j == 0 || depsMono(K - 1, j - 1, K, in, out)) && (time <= ? * K + ?)
  })

  def fillColumn(i: BigInt, j: BigInt, K: BigInt): Unit = {
    require(i >= 0 && j >= 0 && K >= i + 1 && (j == 0 || deps(K - 1, j - 1, K)))
    val v = viterbi(i, j, K)
    if(i != K - 1) fillColumn(i + 1, j, K)
  } ensuring(time <= ? * ((K - i) * K) + ?)

  def fillTable(j: BigInt, T: BigInt, K: BigInt): Unit = {
    require(j >= 0 && T >= j + 1 && K >= 1 && (j == 0 || deps(K - 1, j - 1, K)))
    val s = fillColumn(0, j, K)
    if(j != T - 1) fillTable(j + 1, T, K)
  } ensuring(time <= ? *((K * K) * (T - j)) + ?)

  def viterbiSols(T: BigInt, K: BigInt): Unit = {
    require(T >= 1 && K >= 1)
    fillTable(0, T, K)
  } ensuring(deps(K - 1, T - 1, K) && time <= ? * ((K * K) * T) + ?)

}

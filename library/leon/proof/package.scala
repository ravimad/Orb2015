/* Copyright 2009-2016 EPFL, Lausanne */

package leon

import leon.annotation._
import leon.lang._
import scala.language.implicitConversions

import leon.proof.Internal._

package object proof {

  @library
  @isabelle.typ(name = "Leon_Types.proof_ops")
  @isabelle.constructor(name = "Leon_Types.proof_ops.Proof_Ops")
  case class ProofOps(prop: Boolean) {
    def because(proof: Boolean): Boolean = proof && prop
    def neverHolds: Boolean = {
      require(!prop)
      !prop
    }
  }

  @library
  implicit def boolean2ProofOps(prop: Boolean): ProofOps = ProofOps(prop)

  @library
  def trivial: Boolean = true

  @library
  def by(proof: Boolean)(prop: Boolean): Boolean =
    proof && prop

  @library
  def check(prop: Boolean): Boolean = {
    require(prop)
    prop
  }

  /**
   * Relational reasoning.
   *
   *         {
   *           ((y :: ys) :+ x).last   ^^ _ == _ ^^| trivial         |
   *           (y :: (ys :+ x)).last   ==| trivial         |
   *           (ys :+ x).last          ==| snocLast(ys, x) |
   *           x
   *         }.qed
   */
  @library
  @isabelle.typ(name = "Leon_Types.rel_reasoning")
  @isabelle.constructor(name = "Leon_Types.rel_reasoning.Rel_Reasoning")
  case class RelReasoning[A](x: A, prop: Boolean) {

    def ^^[B](r: (A, B) => Boolean): WithRel[A, B] = WithRel(x, r, prop)

    /** Short-hand for equational reasoning. */
    def ==|(proof: Boolean): WithProof[A, A] = {
      require(proof)
      WithProof(x, _ == _, proof, prop)
    }

    def qed: Boolean = prop
  }

  @library
  implicit def any2RelReasoning[A](x: A): RelReasoning[A] =
    RelReasoning(x, true)

}


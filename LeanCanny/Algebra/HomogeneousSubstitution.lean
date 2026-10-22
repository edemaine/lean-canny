/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Weighted homogeneous substitution into ordinary homogeneous polynomials

Variables of weight zero may be mapped to coefficient constants; weight-one
variables may be mapped to new variables. This turns a partial homogenization
into an ordinary homogeneous polynomial over a parameter coefficient ring.
-/

@[expose] public section

namespace LeanCanny.Algebra.HomogeneousSubstitution
open MvPolynomial
open scoped BigOperators

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S]

theorem homogeneous_eval₂ (w : σ → ℕ) (D : ℕ) (p : MvPolynomial σ R)
    (hp : p.IsWeightedHomogeneous w D) (φ : R →+* S) (x : σ → MvPolynomial τ S)
    (hx : ∀ i, (x i).IsHomogeneous (w i)) :
    (p.eval₂ (MvPolynomial.C.comp φ) x).IsHomogeneous D := by
  classical
  rw [p.as_sum, MvPolynomial.eval₂_sum]
  apply IsHomogeneous.sum
  intro e he
  have hd : Finsupp.weight w e = D := hp (MvPolynomial.mem_support_iff.mp he)
  rw [MvPolynomial.eval₂_monomial]
  change (C (φ (p.coeff e)) * e.prod (fun i k => x i ^ k)).IsHomogeneous D
  have hprod := IsHomogeneous.prod e.support (fun i => x i ^ e i) (fun i => w i * e i)
    (fun i _ => (hx i).pow (e i))
  have hdegree : (∑ i ∈ e.support, w i * e i) = D := by
    simpa only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.mul_comm] using hd
  rw [hdegree] at hprod
  exact hprod.C_mul _

end LeanCanny.Algebra.HomogeneousSubstitution

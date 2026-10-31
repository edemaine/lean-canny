/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogeneousSubstitution
public import Mathlib.Algebra.MvPolynomial.Monad

/-! # Coordinate-dependent powers and parameter degree control

Each retained scalar parameter may have its own power, fixed when it is
introduced. Substitution turns its weighted degree into an ordinary degree
bound while preserving evaluation at the corresponding powered point.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoordinatePowerSubstitution
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable {σ R : Type*} [CommSemiring R]

noncomputable def substitute (w : σ → ℕ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  bind₁ (fun i => X i ^ w i)

theorem substitute_C (w : σ → ℕ) (r : R) : substitute w (C r) = C r :=
  bind₁_C_right _ _

theorem substitute_X (w : σ → ℕ) (i : σ) : substitute w (X i : MvPolynomial σ R) = X i ^ w i :=
  bind₁_X_right _ _

theorem eval_substitute {K : Type*} [CommSemiring K] (φ : R →+* K) (w : σ → ℕ)
    (p : MvPolynomial σ R) (z : σ → K) :
    (substitute w p).eval₂ φ z = p.eval₂ φ (fun i => z i ^ w i) := by
  simpa only [substitute, coe_eval₂Hom, eval₂_pow, eval₂_X] using
    eval₂Hom_bind₁ φ z (fun i => (X i : MvPolynomial σ R) ^ w i) p

theorem homogeneous (w : σ → ℕ) (D : ℕ) (p : MvPolynomial σ R)
    (hp : p.IsWeightedHomogeneous w D) : (substitute w p).IsHomogeneous D := by
  have H := HomogeneousSubstitution.homogeneous_eval₂ w D p hp (RingHom.id R)
    (fun i => (X i : MvPolynomial σ R) ^ w i)
    (fun i => by simpa only [Nat.one_mul] using (isHomogeneous_X (R := R) i).pow (w i))
  change (eval₂ C (fun i => (X i : MvPolynomial σ R) ^ w i) p).IsHomogeneous D
  simpa only [RingHom.comp_id] using H

theorem degree_le_weighted (w : σ → ℕ) (p : MvPolynomial σ R) :
    (substitute w p).totalDegree ≤ p.weightedTotalDegree w := by
  conv_lhs => rw [p.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  exact (homogeneous w _ (monomial e (p.coeff e))
    (isWeightedHomogeneous_monomial w e (p.coeff e) rfl)).totalDegree_le.trans (Finset.le_sup he)

theorem degree_le [Fintype σ] (w : σ → ℕ) (p : MvPolynomial σ R) (W : ℕ) (hw : ∀ i, w i ≤ W) :
    (substitute w p).totalDegree ≤ W * p.totalDegree := by
  apply (degree_le_weighted w p).trans
  apply Finset.sup_le
  intro e he
  calc
    Finsupp.weight w e ≤ W * e.degree := by
      rw [Finsupp.weight_eq_sum, Finsupp.degree_eq_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      simpa only [smul_eq_mul, Nat.mul_comm] using Nat.mul_le_mul_left (e i) (hw i)
    _ ≤ W * p.totalDegree := Nat.mul_le_mul_left W (le_totalDegree he)

end LeanCanny.Algebra.CoordinatePowerSubstitution

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCriticalPowerSystem

/-! # The original Jacobian retained under multiplier power substitution

The Lagrange Jacobian depends on ambient coordinates and objective parameters,
but not on multipliers or fixed height levels. Keeping this determinant as
the bad-root polynomial tests regularity of the original stage even when
some substituted multiplier coordinates vanish.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineCriticalOriginalJacobian
open MvPolynomial FlatAffineCriticalStage AffineCriticalPowerSystem
open scoped Classical BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {K L : Type*} {n : ℕ} [Field K] [Field L] [Algebra K L]

noncomputable def entry (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) : Matrix (Variables n) (Variables n)
      (MvPolynomial (Variables n) (MvPolynomial (Fin n) K))
  | .inl i, .inl k => spatial (pderiv k (pderiv i p))
  | .inl i, .inr j => -C (Fin.cases (X i) (fun r => C (A r i)) j)
  | .inr j, .inl k => Fin.cases (spatial (pderiv k p))
      (fun r => C (C (if r ∈ s then A r k else 0))) j
  | .inr j, .inr m => C (C (Fin.cases 0
      (fun r => if r ∈ s then 0 else if r.succ = m then 1 else 0) j))

noncomputable def jacobian (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) : MvPolynomial (Variables n) (MvPolynomial (Fin n) K) := (entry p s A).det

theorem entry_degree (p : MvPolynomial (Fin n) K) (D : ℕ) (hp : p.totalDegree ≤ D)
    (s : Finset (Fin n)) (A : Fin n → Fin n → K) (r c : Variables n) :
    (entry p s A r c).totalDegree ≤ D := by
  cases r with
  | inl i =>
    cases c with
    | inl k =>
      exact (spatial_degree (pderiv k (pderiv i p))).trans
        ((PartialDerivativeDegree.degree_le _ _).trans ((Nat.sub_le _ _).trans
          ((PartialDerivativeDegree.degree_le _ _).trans ((Nat.sub_le _ _).trans hp))))
    | inr j => simp only [entry, totalDegree_neg, totalDegree_C]; exact Nat.zero_le D
  | inr j =>
    cases c with
    | inl k =>
      refine Fin.cases ?_ (fun r => ?_) j
      · exact (spatial_degree _).trans ((PartialDerivativeDegree.degree_le _ _).trans ((Nat.sub_le _ _).trans hp))
      · simp only [entry, Fin.cases_succ, totalDegree_C]; exact Nat.zero_le D
    | inr m => simp only [entry, totalDegree_C]; exact Nat.zero_le D

theorem degree_le (p : MvPolynomial (Fin n) K) (D : ℕ) (hp : p.totalDegree ≤ D)
    (s : Finset (Fin n)) (A : Fin n → Fin n → K) :
    (jacobian p s A).totalDegree ≤ (2 * n + 1) * D := by
  rw [jacobian, Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro π _
  rw [Units.smul_def]
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _j : Variables n, D := Finset.sum_le_sum fun j _ => entry_degree p D hp s A (π j) j
    _ = (2 * n + 1) * D := by simp only [Finset.sum_const, Finset.card_univ, variables_card, smul_eq_mul]

theorem constant_parameter_degree (q : MvPolynomial (Fin n) K) (E : ℕ) (hq : q.totalDegree ≤ E) :
    NestedTotalDegree.Bound (C q : MvPolynomial (Variables n) (MvPolynomial (Fin n) K)) E := by
  intro e
  rw [coeff_C]
  split_ifs
  · exact hq
  · simp

theorem entry_parameter_degree (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (r c : Variables n) : NestedTotalDegree.Bound (entry p s A r c) 1 := by
  cases r with
  | inl i =>
    cases c with
    | inl k => exact AffineCriticalConeSystem.lift_parameter_degree _ _
    | inr j =>
      apply NestedTotalDegree.neg
      apply constant_parameter_degree
      refine Fin.cases ?_ (fun r => ?_) j <;> simp
  | inr j =>
    cases c with
    | inl k =>
      refine Fin.cases ?_ (fun r => ?_) j
      · exact AffineCriticalConeSystem.lift_parameter_degree _ _
      · apply constant_parameter_degree; simp
    | inr m => apply constant_parameter_degree; simp

theorem parameter_degree (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) : NestedTotalDegree.Bound (jacobian p s A) (2 * n + 1) := by
  have H := NestedTotalDegree.det (entry p s A) 1 (entry_parameter_degree p s A)
  simpa only [jacobian, variables_card, Nat.mul_one] using H

theorem eval_matrix (φ : MvPolynomial (Fin n) K →+* L) (hφ : φ.comp C = algebraMap K L)
    (p : MvPolynomial (Fin n) K) (s : Finset (Fin n)) (A : Fin n → Fin n → K) (z : Variables n → L) :
    (entry p s A).map (eval₂Hom φ z) =
      GenericAffineCriticalJacobian.matrix p s A (fun i => φ (X i)) (z ∘ Sum.inl) := by
  have hC (k : K) : φ (C k) = algebraMap K L k := congrArg (fun f : K →+* L => f k) hφ
  apply Matrix.ext
  intro r c
  cases r with
  | inl i =>
    cases c with
    | inl k => exact eval_spatial φ hφ _ z
    | inr j =>
      refine Fin.cases ?_ (fun r => ?_) j <;>
        simp only [Matrix.map_apply, entry, Fin.cases_zero, Fin.cases_succ, coe_eval₂Hom,
          eval₂_neg, eval₂_C, hC, GenericAffineCriticalJacobian.matrix]
  | inr j =>
    refine Fin.cases ?_ (fun r => ?_) j
    · cases c with
      | inl k => exact eval_spatial φ hφ _ z
      | inr m =>
        change (C (C (0 : K)) : MvPolynomial (Variables n) (MvPolynomial (Fin n) K)).eval₂ φ z = 0
        simp
    · cases c with
      | inl k =>
        change (C (C (if r ∈ s then A r k else 0)) :
          MvPolynomial (Variables n) (MvPolynomial (Fin n) K)).eval₂ φ z =
            if r ∈ s then algebraMap K L (A r k) else 0
        by_cases hr : r ∈ s <;> simp [hr, hC]
      | inr m =>
        change (C (C (if r ∈ s then 0 else if r.succ = m then 1 else 0 : K)) :
          MvPolynomial (Variables n) (MvPolynomial (Fin n) K)).eval₂ φ z =
            if r ∈ s then 0 else if r.succ = m then 1 else 0
        by_cases hr : r ∈ s <;> by_cases hm : r.succ = m <;> simp [hr, hm]

theorem eval_jacobian (φ : MvPolynomial (Fin n) K →+* L) (hφ : φ.comp C = algebraMap K L)
    (p : MvPolynomial (Fin n) K) (s : Finset (Fin n)) (A : Fin n → Fin n → K) (z : Variables n → L) :
    (jacobian p s A).eval₂ φ z =
      (GenericAffineCriticalJacobian.matrix p s A (fun i => φ (X i)) (z ∘ Sum.inl)).det := by
  change (eval₂Hom φ z) (entry p s A).det = _
  rw [RingHom.map_det]
  change ((entry p s A).map (eval₂Hom φ z)).det = _
  rw [eval_matrix φ hφ]

/-- Genericity is checked for the original Lagrange matrix, including
power-coordinate roots whose multiplier coordinates are zero. -/
theorem generic_regular [CharZero K] (φ : MvPolynomial (Fin n) K →+* L)
    (hφ : φ.comp C = algebraMap K L) (hinj : Function.Injective φ)
    (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K)
    (hslice : ∀ x : Fin n → L, aeval x p = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = algebraMap K L (β r)) →
      GenericAffineCriticalJacobian.ConstraintIndependent p s A x)
    (z : Variables n → L) (hz : ∀ j, (AffineCriticalPowerSystem.rows p D s A β j).eval₂ φ z = 0) :
    (jacobian p s A).eval₂ φ z ≠ 0 := by
  obtain ⟨hp, hl, hg, hu⟩ := (AffineCriticalPowerSystem.roots_iff φ hφ p D s A β z).mp hz
  have hc := hslice (z ∘ Sum.inl) hp hl
  have hμ := GenericAffineCriticalJacobian.multiplier_ne_zero p s A (fun i => φ (X i))
    (z ∘ Sum.inl) (fun r => z (Sum.inr r) ^ (D - 1)) hg hu hc
  rw [eval_jacobian φ hφ]
  exact GenericAffineCriticalJacobian.det_ne_zero p s A β (fun i => φ (X i)) (z ∘ Sum.inl)
    (fun r => z (Sum.inr r) ^ (D - 1)) (AffineCriticalConeSystem.independent_parameters φ hφ hinj)
    hp hl hg hu hμ hc

end LeanCanny.Algebra.AffineCriticalOriginalJacobian

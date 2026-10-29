/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoordinateDerivation
public import LeanCanny.Algebra.CriticalValueAlgebraic
public import LeanCanny.Algebra.FlatAffineCriticalRegularity
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Generic objective coefficients give regular affine critical stages

Direction derivations span the gradient rows of the spatial Jacobian when
the new multiplier is nonzero. Independence of the slice constraint rows
then eliminates the remaining left kernel. Source and old-height levels
are fixed elements of the coefficient field.
-/

@[expose] public section
namespace LeanCanny.Algebra.GenericAffineCriticalJacobian
open MvPolynomial Matrix FlatAffineCriticalStage
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {K L : Type*} {n : ℕ} [Field K] [Field L] [Algebra K L]

noncomputable def matrix (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (v x : Fin n → L) : Matrix (Variables n) (Variables n) L
  | .inl i, .inl k => aeval x (pderiv k (pderiv i p))
  | .inl i, .inr j => -Fin.cases (v i) (fun r => algebraMap K L (A r i)) j
  | .inr j, .inl k => Fin.cases (aeval x (pderiv k p))
      (fun r => if r ∈ s then algebraMap K L (A r k) else 0) j
  | .inr j, .inr m => Fin.cases 0
      (fun r => if r ∈ s then 0 else if r.succ = m then 1 else 0) j

def ConstraintIndependent (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (x : Fin n → L) : Prop :=
  ∀ (c0 : L) (c : Fin n → L), (∀ j, j ∉ s → c j = 0) →
    (∀ i, c0 * aeval x (pderiv i p) + ∑ j, c j * algebraMap K L (A j i) = 0) →
    c0 = 0 ∧ ∀ j, c j = 0

noncomputable def constraintMatrix (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (x : Fin n → L) : Matrix (Option s) (Fin n) L
  | none, i => aeval x (pderiv i p)
  | some j, i => algebraMap K L (A j.val i)

theorem independent_of_surjective (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (x : Fin n → L)
    (h : Function.Surjective (constraintMatrix p s A x).mulVec) : ConstraintIndependent p s A x := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h
  intro c0 c hc hz
  let w : Option s → L := fun o => o.elim c0 (fun j => c j.val)
  have hw : w ᵥ* constraintMatrix p s A x = 0 := by
    funext i
    change (∑ j, w j * constraintMatrix p s A x j i) = 0
    rw [Fintype.sum_option]
    change c0 * aeval x (pderiv i p) + ∑ j : s, c j.val * algebraMap K L (A j.val i) = 0
    have hs : (∑ j : Fin n, c j * algebraMap K L (A j i)) =
        ∑ j ∈ s, c j * algebraMap K L (A j i) := by
      apply (Finset.sum_subset (Finset.subset_univ s) ?_).symm
      intro j _ hj
      rw [hc j hj, zero_mul]
    have H := hz i
    rw [hs, ← Finset.sum_attach s (fun j => c j * algebraMap K L (A j i))] at H
    exact H
  have hw0 := congrArg (fun r => r ᵥ* B) hw
  rw [Matrix.vecMul_vecMul, hB, Matrix.vecMul_one, Matrix.zero_vecMul] at hw0
  refine ⟨congrFun hw0 none, fun j => ?_⟩
  by_cases hj : j ∈ s
  · exact congrFun hw0 (some ⟨j, hj⟩)
  · exact hc j hj


theorem derivation_column (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (b : Fin n → K) (v x : Fin n → L) (μ : Fin (n + 1) → L)
    (δ : Derivation K L L) (j : Fin n)
    (hv : ∀ i, δ (v i) = if i = j then 1 else 0)
    (hp : aeval x p = 0)
    (hl : ∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = algebraMap K L (b r))
    (hg : ∀ i, aeval x (pderiv i p) = v i * μ 0 + ∑ r, algebraMap K L (A r i) * μ r.succ)
    (hu : ∀ r, r ∉ s → μ r.succ = 0) :
    (matrix p s A v x).mulVec (Sum.elim (fun k => δ (x k)) (fun r => δ (μ r))) =
      Pi.single (Sum.inl j) (μ 0) := by
  funext c
  cases c with
  | inl i =>
    have h := congrArg δ (hg i)
    simp only [map_add, map_sum, Derivation.leibniz, smul_eq_mul,
      Derivation.map_algebraMap, mul_zero, add_zero, hv, CriticalValueAlgebraic.chain_rule] at h
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, matrix, Sum.elim_inl, Sum.elim_inr,
      Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, neg_mul, Finset.sum_neg_distrib]
    by_cases hij : i = j
    · subst i
      simp only [ite_true] at h
      simp only [Pi.single_eq_same]
      linear_combination h
    · simp only [hij, ite_false] at h
      simp only [Pi.single_apply, Sum.inl.injEq, hij, ite_false]
      linear_combination h
  | inr r =>
    refine Fin.cases ?_ (fun r => ?_) r
    · have h := congrArg δ hp
      rw [CriticalValueAlgebraic.chain_rule, map_zero] at h
      simpa only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, matrix, Fin.cases_zero,
        Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero,
        Pi.single_apply, reduceCtorEq, ite_false] using h
    · by_cases hr : r ∈ s
      · have h := congrArg δ (hl r hr)
        simp only [map_sum, Derivation.leibniz, smul_eq_mul, Derivation.map_algebraMap,
          mul_zero, add_zero] at h
        simpa only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, matrix, Fin.cases_succ,
          hr, ite_true, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero,
          Pi.single_apply, reduceCtorEq, ite_false] using h
      · have h := congrArg δ (hu r hr)
        rw [map_zero] at h
        simpa only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, matrix, Fin.cases_succ,
          hr, ite_false, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, zero_add,
          Pi.single_apply, reduceCtorEq, ite_false, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h

theorem multiplier_ne_zero (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (v x : Fin n → L) (μ : Fin (n + 1) → L)
    (hg : ∀ i, aeval x (pderiv i p) = v i * μ 0 + ∑ r, algebraMap K L (A r i) * μ r.succ)
    (hu : ∀ r, r ∉ s → μ r.succ = 0) (hconstraint : ConstraintIndependent p s A x) : μ 0 ≠ 0 := by
  intro hμ
  have hc := hconstraint 1 (fun r => -μ r.succ)
    (fun r hr => by rw [hu r hr, neg_zero]) (fun i => by
      have H := hg i
      rw [hμ, mul_zero, zero_add] at H
      have hs : (∑ r, (-μ r.succ) * algebraMap K L (A r i)) =
          -∑ r, algebraMap K L (A r i) * μ r.succ := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro r _
        ring
      rw [one_mul, hs, H, add_neg_cancel])
  exact one_ne_zero hc.1

theorem det_ne_zero [CharZero K] (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (b : Fin n → K) (v x : Fin n → L) (μ : Fin (n + 1) → L)
    (hind : AlgebraicIndependent K v) (hp : aeval x p = 0)
    (hl : ∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = algebraMap K L (b r))
    (hg : ∀ i, aeval x (pderiv i p) = v i * μ 0 + ∑ r, algebraMap K L (A r i) * μ r.succ)
    (hu : ∀ r, r ∉ s → μ r.succ = 0) (hμ : μ 0 ≠ 0)
    (hconstraint : ConstraintIndependent p s A x) : (matrix p s A v x).det ≠ 0 := by
  choose δ hδ using fun j => CoordinateDerivation.exists_of_independent hind j
  let M := matrix p s A v x
  have hkernel (w : Variables n → L) (hw : w ᵥ* M = 0) : w = 0 := by
    have hgrad (j : Fin n) : w (Sum.inl j) = 0 := by
      have he : w ⬝ᵥ (M *ᵥ Sum.elim (fun k => δ j (x k)) (fun r => δ j (μ r))) = 0 := by
        rw [Matrix.dotProduct_mulVec, hw]
        simp
      rw [derivation_column p s A b v x μ (δ j) j (hδ j) hp hl hg hu, dotProduct_single] at he
      exact (mul_eq_zero.mp he).resolve_right hμ
    have hinactive (j : Fin n) (hj : j ∉ s) : w (Sum.inr j.succ) = 0 := by
      have H := congrFun hw (Sum.inr j.succ)
      change (∑ r, w r * M r (Sum.inr j.succ)) = 0 at H
      simp only [Fintype.sum_sum_type, M, matrix, hgrad, zero_mul, Finset.sum_const_zero,
        zero_add, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, mul_zero] at H
      have he : (∑ r : Fin n, w (Sum.inr r.succ) *
          (if r ∈ s then 0 else if r.succ = j.succ then 1 else 0)) = w (Sum.inr j.succ) := by
        rw [Finset.sum_eq_single j]
        · simp only [hj, ite_false, ite_true, mul_one]
        · intro r _ hr
          simp only [Fin.succ_inj, hr, ite_false, ite_self, mul_zero]
        · simp
      rw [he] at H
      exact H
    have hc := hconstraint (w (Sum.inr 0)) (fun r => w (Sum.inr r.succ)) hinactive (fun i => by
      have H := congrFun hw (Sum.inl i)
      change (∑ r, w r * M r (Sum.inl i)) = 0 at H
      simp only [Fintype.sum_sum_type, M, matrix, hgrad, zero_mul, Finset.sum_const_zero,
        zero_add, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ] at H
      have he : (∑ r : Fin n, w (Sum.inr r.succ) * (if r ∈ s then algebraMap K L (A r i) else 0)) =
          ∑ r : Fin n, w (Sum.inr r.succ) * algebraMap K L (A r i) := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases hr : r ∈ s
        · rw [ite_eq_left hr]
        · rw [ite_eq_right hr, hinactive r hr, zero_mul, zero_mul]
      rw [he] at H
      exact H)
    funext r
    cases r with
    | inl i => exact hgrad i
    | inr j => exact Fin.cases hc.1 (fun r => hc.2 r) j
  have hinj : Function.Injective M.vecMul := by
    intro w z he
    change w ᵥ* M = z ᵥ* M at he
    apply sub_eq_zero.mp
    apply hkernel
    rw [Matrix.sub_vecMul, he, sub_self]
  exact ((M.isUnit_iff_isUnit_det).mp (Matrix.vecMul_injective_iff_isUnit.mp hinj)).ne_zero

end LeanCanny.Algebra.GenericAffineCriticalJacobian

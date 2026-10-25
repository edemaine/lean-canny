/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PartialDerivativeDegree
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Normalized kernel charts for singular polynomial roots

A singular square Jacobian has a nonzero kernel vector. Normalizing one of
its coordinates replaces determinant evaluation by bilinear equations. The
Jacobian's polynomial degree drops by at least one in every determinant row.
-/

@[expose] public section
namespace LeanCanny.Algebra.JacobianKernelCharts
open MvPolynomial
open scoped Classical BigOperators Matrix

variable {n : ℕ}

theorem det_zero_iff {K : Type*} [Field K] (M : Matrix (Fin n) (Fin n) K) :
    M.det = 0 ↔ ∃ i : Fin n, ∃ v : Fin n → K, v i = 1 ∧ M *ᵥ v = 0 := by
  constructor
  · intro h
    obtain ⟨v, hv, hm⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have hvi : v i ≠ 0 := by simpa only [Pi.zero_apply] using hi
    refine ⟨i, (v i)⁻¹ • v, ?_, ?_⟩
    · exact inv_mul_cancel₀ hvi
    · rw [Matrix.mulVec_smul, hm, smul_zero]
  · rintro ⟨i, v, hi, hm⟩
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, ?_, hm⟩
    intro hz
    have hh := congrFun hz i
    rw [hi, Pi.zero_apply] at hh
    exact one_ne_zero hh

noncomputable def jacobian {R : Type*} [CommRing R] (p : Fin n → MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) R := Matrix.det (Matrix.of (fun i j => pderiv j (p i)))

noncomputable def matrix {R K : Type*} [CommRing R] [CommRing K] (φ : R →+* K)
    (p : Fin n → MvPolynomial (Fin n) R) (x : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of (fun i j => (pderiv j (p i)).eval₂ φ x)

theorem eval_jacobian {R K : Type*} [CommRing R] [CommRing K] (φ : R →+* K)
    (p : Fin n → MvPolynomial (Fin n) R) (x : Fin n → K) :
    (jacobian p).eval₂ φ x = (matrix φ p x).det := by
  change (eval₂Hom φ x) (Matrix.det _) = _
  rw [RingHom.map_det]
  rfl

theorem regular_iff_charts {R K : Type*} [CommRing R] [Field K] (φ : R →+* K)
    (p : Fin n → MvPolynomial (Fin n) R) :
    (∀ x : Fin n → K, (∀ j, (p j).eval₂ φ x = 0) → (jacobian p).eval₂ φ x ≠ 0) ↔
      ∀ i : Fin n, ¬ ∃ x v : Fin n → K, v i = 1 ∧ (∀ j, (p j).eval₂ φ x = 0) ∧ matrix φ p x *ᵥ v = 0 := by
  constructor
  · intro h i ⟨x, v, hi, hx, hv⟩
    apply h x hx
    rw [eval_jacobian, det_zero_iff]
    exact ⟨i, v, hi, hv⟩
  · intro h x hx hz
    rw [eval_jacobian, det_zero_iff] at hz
    obtain ⟨i, v, hi, hv⟩ := hz
    exact h i ⟨x, v, hi, hx, hv⟩

theorem degree_le {R : Type*} [CommRing R] [Nontrivial R]
    (p : Fin n → MvPolynomial (Fin n) R) (D : ℕ) (hp : ∀ i, (p i).totalDegree ≤ D) :
    (jacobian p).totalDegree ≤ n * (D - 1) := by
  rw [jacobian, Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro π _
  rw [Units.smul_def]
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  exact (Finset.sum_le_sum fun j _ =>
    (PartialDerivativeDegree.degree_le _ _).trans (Nat.sub_le_sub_right (hp (π j)) 1)).trans_eq (by simp)

end LeanCanny.Algebra.JacobianKernelCharts

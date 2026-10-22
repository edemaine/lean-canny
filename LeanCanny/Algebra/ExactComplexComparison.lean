/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ExactComplexDeterminant

/-! # Independence of the alternating determinant of a chain comparison

Two degreewise equivalences intertwining the same source and target
differentials have equal alternating determinant quotients when the
source complex is finite and exact. Their quotient is a chain automorphism
of the source, whose even and odd determinant products are equal.
-/

@[expose] public section

namespace LeanCanny.Algebra.ExactComplexComparison
open scoped Classical
variable {K : Type*} [Field K] (V : ℕ → Type*) [∀ k, AddCommGroup (V k)] [∀ k, Module K (V k)]

noncomputable def determinantRatio (f : (k : ℕ) → V k →ₗ[K] V k) (N : ℕ) : K :=
  AlternatingProducts.ratio (fun k => (f k).det) (N + 1)

theorem determinantRatio_comp (f g : (k : ℕ) → V k →ₗ[K] V k) (N : ℕ) :
    determinantRatio V (fun k => (f k).comp (g k)) N = determinantRatio V f N * determinantRatio V g N := by
  simp only [determinantRatio, LinearMap.det_comp]
  exact AlternatingProducts.ratio_mul _ _ _

theorem determinantRatio_id (N : ℕ) : determinantRatio V (fun k => (LinearMap.id : V k →ₗ[K] V k)) N = 1 := by
  simp only [determinantRatio, LinearMap.det_id]
  exact AlternatingProducts.ratio_one _

theorem equivalence_det_ne_zero {M : Type*} [AddCommGroup M] [Module K M] (e : M ≃ₗ[K] M) :
    e.toLinearMap.det ≠ 0 := by
  have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.apply_symm_apply x
  have hd := congrArg LinearMap.det he
  rw [LinearMap.det_comp, LinearMap.det_id] at hd
  exact left_ne_zero_of_mul_eq_one hd

theorem determinantRatio_eq_one [∀ k, FiniteDimensional K (V k)]
    (d : (k : ℕ) → V (k + 1) →ₗ[K] V k) (f : (k : ℕ) → V k →ₗ[K] V k)
    (h : ∀ k, (d k).comp (f (k + 1)) = (f k).comp (d k))
    (hex : ∀ k, LinearMap.ker (d k) = LinearMap.range (d (k + 1))) (hs : Function.Surjective (d 0))
    (N : ℕ) [Subsingleton (V (N + 1))] (hdet : ∀ k, (f k).det ≠ 0) : determinantRatio V f N = 1 := by
  rw [determinantRatio, AlternatingProducts.ratio,
    ExactComplexDeterminant.even_det_eq_odd_det V d f h hex hs N]
  exact div_self (AlternatingProducts.oddProduct_ne_zero _ _ hdet)

theorem inverse_chain (d e : (k : ℕ) → V (k + 1) →ₗ[K] V k) (G : (k : ℕ) → V k ≃ₗ[K] V k)
    (hG : ∀ k, (e k).comp (G (k + 1)).toLinearMap = (G k).toLinearMap.comp (d k)) (k : ℕ) :
    (d k).comp (G (k + 1)).symm.toLinearMap = (G k).symm.toLinearMap.comp (e k) := by
  apply LinearMap.ext
  intro x
  have hx := congrArg (G k).symm (LinearMap.congr_fun (hG k) ((G (k + 1)).symm x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_apply_apply] at hx
  exact hx.symm

theorem comparison_invariant [∀ k, FiniteDimensional K (V k)]
    (d e : (k : ℕ) → V (k + 1) →ₗ[K] V k) (F G : (k : ℕ) → V k ≃ₗ[K] V k)
    (hF : ∀ k, (e k).comp (F (k + 1)).toLinearMap = (F k).toLinearMap.comp (d k))
    (hG : ∀ k, (e k).comp (G (k + 1)).toLinearMap = (G k).toLinearMap.comp (d k))
    (hex : ∀ k, LinearMap.ker (d k) = LinearMap.range (d (k + 1))) (hs : Function.Surjective (d 0))
    (N : ℕ) [Subsingleton (V (N + 1))] :
    determinantRatio V (fun k => (F k).toLinearMap) N = determinantRatio V (fun k => (G k).toLinearMap) N := by
  let A : (k : ℕ) → V k →ₗ[K] V k := fun k => (G k).symm.toLinearMap.comp (F k).toLinearMap
  have hA (k : ℕ) : (d k).comp (A (k + 1)) = (A k).comp (d k) := by
    calc
      _ = ((d k).comp (G (k + 1)).symm.toLinearMap).comp (F (k + 1)).toLinearMap :=
        (LinearMap.comp_assoc _ _ _).symm
      _ = ((G k).symm.toLinearMap.comp (e k)).comp (F (k + 1)).toLinearMap := by rw [inverse_chain V d e G hG k]
      _ = (G k).symm.toLinearMap.comp ((e k).comp (F (k + 1)).toLinearMap) := LinearMap.comp_assoc _ _ _
      _ = (G k).symm.toLinearMap.comp ((F k).toLinearMap.comp (d k)) := by rw [hF k]
      _ = _ := (LinearMap.comp_assoc _ _ _).symm
  have hAdet (k : ℕ) : (A k).det ≠ 0 := by
    dsimp only [A]
    rw [LinearMap.det_comp]
    exact mul_ne_zero (equivalence_det_ne_zero (G k).symm) (equivalence_det_ne_zero (F k))
  have hAratio := determinantRatio_eq_one V d A hA hex hs N hAdet
  have hAid : determinantRatio V (fun k => (G k).symm.toLinearMap) N *
      determinantRatio V (fun k => (G k).toLinearMap) N = 1 := by
    rw [← determinantRatio_comp]
    have hid : (fun k => (G k).symm.toLinearMap.comp (G k).toLinearMap) =
        (fun k => (LinearMap.id : V k →ₗ[K] V k)) := by
      funext k
      apply LinearMap.ext
      intro x
      exact (G k).symm_apply_apply x
    rw [hid, determinantRatio_id]
  apply mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hAid)
  rw [← determinantRatio_comp]
  exact hAratio.trans hAid.symm

end LeanCanny.Algebra.ExactComplexComparison

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ExactComplexComparison

/-! # Transporting chain comparisons to different graded coordinates

Simultaneous conjugation of the source and target differentials transports
a chain comparison and preserves its alternating determinant ratio. Exact
comparison invariance then compares it to any comparison in the new
coordinates. No orientation or basis sign is introduced.
-/

@[expose] public section

namespace LeanCanny.Algebra.ExactComplexTransport
open scoped Classical
variable {K : Type*} [Field K] (V W : ℕ → Type*)
  [∀ k, AddCommGroup (V k)] [∀ k, Module K (V k)]
  [∀ k, AddCommGroup (W k)] [∀ k, Module K (W k)]

noncomputable def conjugate (T : (k : ℕ) → V k ≃ₗ[K] W k) (F : (k : ℕ) → V k ≃ₗ[K] V k) (k : ℕ) :
    W k ≃ₗ[K] W k := ((T k).symm.trans (F k)).trans (T k)

theorem conjugate_toLinearMap (T : (k : ℕ) → V k ≃ₗ[K] W k) (F : (k : ℕ) → V k ≃ₗ[K] V k) (k : ℕ) :
    (conjugate V W T F k).toLinearMap =
      (T k).toLinearMap.comp ((F k).toLinearMap.comp (T k).symm.toLinearMap) := rfl

theorem inverse_intertwines (d : (k : ℕ) → V (k + 1) →ₗ[K] V k)
    (e : (k : ℕ) → W (k + 1) →ₗ[K] W k) (T : (k : ℕ) → V k ≃ₗ[K] W k)
    (hT : ∀ k, (e k).comp (T (k + 1)).toLinearMap = (T k).toLinearMap.comp (d k)) (k : ℕ) :
    (d k).comp (T (k + 1)).symm.toLinearMap = (T k).symm.toLinearMap.comp (e k) := by
  apply LinearMap.ext
  intro x
  have hx := congrArg (T k).symm (LinearMap.congr_fun (hT k) ((T (k + 1)).symm x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_apply_apply] at hx
  exact hx.symm

theorem conjugate_chain (d e : (k : ℕ) → V (k + 1) →ₗ[K] V k)
    (d' e' : (k : ℕ) → W (k + 1) →ₗ[K] W k) (T : (k : ℕ) → V k ≃ₗ[K] W k)
    (F : (k : ℕ) → V k ≃ₗ[K] V k)
    (hd : ∀ k, (d' k).comp (T (k + 1)).toLinearMap = (T k).toLinearMap.comp (d k))
    (he : ∀ k, (e' k).comp (T (k + 1)).toLinearMap = (T k).toLinearMap.comp (e k))
    (hF : ∀ k, (e k).comp (F (k + 1)).toLinearMap = (F k).toLinearMap.comp (d k)) (k : ℕ) :
    (e' k).comp (conjugate V W T F (k + 1)).toLinearMap =
      (conjugate V W T F k).toLinearMap.comp (d' k) := by
  apply LinearMap.ext
  intro x
  have hdi : d k ((T (k + 1)).symm x) = (T k).symm (d' k x) :=
    LinearMap.congr_fun (inverse_intertwines V W d d' T hd k) x
  change e' k (T (k + 1) (F (k + 1) ((T (k + 1)).symm x))) = T k (F k ((T k).symm (d' k x)))
  calc
    _ = T k (e k (F (k + 1) ((T (k + 1)).symm x))) := LinearMap.congr_fun (he k) _
    _ = T k (F k (d k ((T (k + 1)).symm x))) :=
      congrArg (T k) (LinearMap.congr_fun (hF k) ((T (k + 1)).symm x))
    _ = _ := congrArg (fun y => T k (F k y)) hdi

theorem determinantRatio_conjugate (T : (k : ℕ) → V k ≃ₗ[K] W k) (F : (k : ℕ) → V k ≃ₗ[K] V k) (N : ℕ) :
    ExactComplexComparison.determinantRatio W (fun k => (conjugate V W T F k).toLinearMap) N =
      ExactComplexComparison.determinantRatio V (fun k => (F k).toLinearMap) N := by
  simp only [ExactComplexComparison.determinantRatio, conjugate_toLinearMap, LinearMap.det_conj]

theorem comparison_invariant [∀ k, FiniteDimensional K (W k)]
    (d e : (k : ℕ) → V (k + 1) →ₗ[K] V k) (d' e' : (k : ℕ) → W (k + 1) →ₗ[K] W k)
    (T : (k : ℕ) → V k ≃ₗ[K] W k) (F : (k : ℕ) → V k ≃ₗ[K] V k) (G : (k : ℕ) → W k ≃ₗ[K] W k)
    (hd : ∀ k, (d' k).comp (T (k + 1)).toLinearMap = (T k).toLinearMap.comp (d k))
    (he : ∀ k, (e' k).comp (T (k + 1)).toLinearMap = (T k).toLinearMap.comp (e k))
    (hF : ∀ k, (e k).comp (F (k + 1)).toLinearMap = (F k).toLinearMap.comp (d k))
    (hG : ∀ k, (e' k).comp (G (k + 1)).toLinearMap = (G k).toLinearMap.comp (d' k))
    (hex : ∀ k, LinearMap.ker (d' k) = LinearMap.range (d' (k + 1))) (hs : Function.Surjective (d' 0))
    (N : ℕ) [Subsingleton (W (N + 1))] :
    ExactComplexComparison.determinantRatio V (fun k => (F k).toLinearMap) N =
      ExactComplexComparison.determinantRatio W (fun k => (G k).toLinearMap) N := by
  have hi := ExactComplexComparison.comparison_invariant W d' e' (conjugate V W T F) G
    (conjugate_chain V W d e d' e' T F hd he hF) hG hex hs N
  rw [determinantRatio_conjugate] at hi
  exact hi

end LeanCanny.Algebra.ExactComplexTransport

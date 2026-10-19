/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.GCDRecovery
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# The parameter polynomial in Canny's primitive-element construction

The inner variable is the separating parameter and the outer variable is
eliminated. Fixed source degrees specify the Sylvester matrix, so specialization
remains valid when the actual degree drops. `projectionResultant` puts `p₂` first;
`cannyResultant` has the report's order and differs by the usual sign.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

section CommRing
variable {R : Type*} [CommRing R]

noncomputable def shiftFamily (p : Polynomial R) (c : ℕ) : Polynomial (Polynomial R) :=
  (p.map C).comp (C X - C (C (c : R)) * X)

noncomputable def projectionResultant (p₁ p₂ : Polynomial R) (c : ℕ) : Polynomial R :=
  (p₂.map C).resultant (shiftFamily p₁ c) p₂.natDegree p₁.natDegree

noncomputable def cannyResultant (p₁ p₂ : Polynomial R) (c : ℕ) : Polynomial R :=
  (shiftFamily p₁ c).resultant (p₂.map C) p₁.natDegree p₂.natDegree

theorem cannyResultant_eq_sign_mul (p₁ p₂ : Polynomial R) (c : ℕ) :
    cannyResultant p₁ p₂ c = C ((-1 : R) ^ (p₁.natDegree * p₂.natDegree)) *
      projectionResultant p₁ p₂ c := by
  rw [cannyResultant, Polynomial.resultant_comm]
  simp only [projectionResultant, map_pow, map_neg, map_one]

end CommRing

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

@[simp] theorem specialize_comp_C (θ : L) :
    ((Polynomial.aeval θ : Polynomial K →ₐ[K] L) : Polynomial K →+* L).comp C = algebraMap K L := by
  ext x
  simp

@[simp] theorem shiftFamily_specialize (p : Polynomial K) (c : ℕ) (θ : L) :
    (shiftFamily p c).map ((Polynomial.aeval θ : Polynomial K →ₐ[K] L) : Polynomial K →+* L) =
      shiftedPolynomial p c θ := by
  simp [shiftFamily, shiftedPolynomial, Polynomial.map_comp, Polynomial.map_map, specialize_comp_C]

theorem projectionResultant_specialize (p₁ p₂ : Polynomial K) (c : ℕ) (θ : L) :
    Polynomial.aeval θ (projectionResultant p₁ p₂ c) =
      (p₂.map (algebraMap K L)).resultant (shiftedPolynomial p₁ c θ) p₂.natDegree p₁.natDegree := by
  change ((Polynomial.aeval θ : Polynomial K →ₐ[K] L) : Polynomial K →+* L)
    ((p₂.map C).resultant (shiftFamily p₁ c) p₂.natDegree p₁.natDegree) = _
  rw [← Polynomial.resultant_map_map, Polynomial.map_map, specialize_comp_C, shiftFamily_specialize]

theorem shiftedPolynomial_natDegree_le (p : Polynomial K) (c : ℕ) (θ : L) :
    (shiftedPolynomial p c θ).natDegree ≤ p.natDegree := by
  have hlinear : (C θ - C (c : L) * X : Polynomial L).natDegree ≤ 1 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp)
      ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)))
  calc
    _ ≤ (p.map (algebraMap K L)).natDegree * (C θ - C (c : L) * X).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ p.natDegree * 1 := by
      rw [Polynomial.natDegree_map]
      exact Nat.mul_le_mul_left _ hlinear
    _ = _ := Nat.mul_one _

theorem projectionResultant_eval_prod (p₁ p₂ : Polynomial K) (c : ℕ) (θ : L)
    (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    Polynomial.aeval θ (projectionResultant p₁ p₂ c) =
      (algebraMap K L p₂.leadingCoeff) ^ p₁.natDegree *
        ((p₂.map (algebraMap K L)).roots.map
          (fun b => Polynomial.aeval (θ - (c : L) * b) p₁)).prod := by
  rw [projectionResultant_specialize]
  simpa only [Polynomial.natDegree_map, Polynomial.leadingCoeff_map, eval_shiftedPolynomial] using
    Polynomial.resultant_eq_prod_eval (p₂.map (algebraMap K L)) (shiftedPolynomial p₁ c θ)
      p₁.natDegree (shiftedPolynomial_natDegree_le p₁ c θ) hs₂

/-- The determinant polynomial vanishes exactly on projected pairs of roots. -/
theorem projectionResultant_roots (p₁ p₂ : Polynomial K) (c : ℕ) (θ : L)
    (h₂ : p₂ ≠ 0) (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    Polynomial.aeval θ (projectionResultant p₁ p₂ c) = 0 ↔
      ∃ a b : L, Polynomial.aeval a p₁ = 0 ∧ Polynomial.aeval b p₂ = 0 ∧ θ = a + (c : L) * b := by
  classical
  have hlc : algebraMap K L p₂.leadingCoeff ≠ 0 :=
    by simpa only [map_zero] using
      (algebraMap K L).injective.ne (mt Polynomial.leadingCoeff_eq_zero.mp h₂)
  rw [projectionResultant_eval_prod p₁ p₂ c θ hs₂, mul_eq_zero]
  simp only [pow_ne_zero _ hlc, false_or]
  constructor
  · intro h
    obtain ⟨b, hb, ha⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h)
    have hb' : Polynomial.aeval b p₂ = 0 := by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using
        (Polynomial.mem_roots (Polynomial.map_ne_zero h₂)).mp hb
    exact ⟨θ - (c : L) * b, b, ha, hb', by ring⟩
  · rintro ⟨a, b, ha, hb, hθ⟩
    apply Multiset.prod_eq_zero_iff.mpr
    apply Multiset.mem_map.mpr
    refine ⟨b, ?_, ?_⟩
    · apply (Polynomial.mem_roots (Polynomial.map_ne_zero h₂)).mpr
      simpa only [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hb
    · rw [hθ]
      simpa only [add_sub_cancel_right] using ha

end LeanCanny.Algebra

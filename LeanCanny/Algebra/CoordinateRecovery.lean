/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SubresultantRecovery
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Coordinate recovery including linear inputs and zero directions

When the second input is linear, its coefficients recover `b` directly. When
only the first input is linear, use the shifted first input. Otherwise use the
first subresultant. A separating root pair with zero direction forces the second
input to be linear, so these branches cover every direction and input degree
under the separating-pair hypotheses.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

noncomputable def coordinateCoefficient {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c r : ℕ) : Polynomial R :=
  if p₂.natDegree = 1 then C (p₂.coeff r)
  else if p₁.natDegree = 1 then (shiftFamily p₁ c).coeff r
  else (recoverySubresultant p₁ p₂ c).coeff r

noncomputable def coordinateNumerator {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c : ℕ) : Polynomial R :=
  if p₂.natDegree = 1 then C (p₂.coeff 0)
  else if p₁.natDegree = 1 then (shiftFamily p₁ c).coeff 0
  else subresultantNumerator p₁ p₂ c

noncomputable def coordinateDenominator {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c : ℕ) : Polynomial R :=
  if p₂.natDegree = 1 then C (p₂.coeff 1)
  else if p₁.natDegree = 1 then (shiftFamily p₁ c).coeff 1
  else subresultantDenominator p₁ p₂ c

theorem coordinateCoefficient_zero {R : Type*} [CommRing R] (p₁ p₂ : Polynomial R) (c : ℕ) :
    coordinateCoefficient p₁ p₂ c 0 = coordinateNumerator p₁ p₂ c := rfl

theorem coordinateCoefficient_one {R : Type*} [CommRing R] (p₁ p₂ : Polynomial R) (c : ℕ) :
    coordinateCoefficient p₁ p₂ c 1 = coordinateDenominator p₁ p₂ c := rfl

theorem linearPolynomial_root_spec {K : Type*} [Field K] (p : Polynomial K) (b : K)
    (hdeg : p.natDegree = 1) (hb : p.eval b = 0) :
    p.coeff 1 ≠ 0 ∧ b = -p.coeff 0 / p.coeff 1 := by
  have hp : p ≠ 0 := by intro h; simp [h] at hdeg
  have hden : p.coeff 1 ≠ 0 := by
    simpa only [Polynomial.leadingCoeff, hdeg] using Polynomial.leadingCoeff_ne_zero.mpr hp
  refine ⟨hden, ?_⟩
  have he := congrArg (fun q : Polynomial K => q.eval b)
    (Polynomial.eq_X_add_C_of_natDegree_le_one hdeg.le)
  rw [hb] at he
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at he
  rw [eq_div_iff hden]
  exact (mul_comm _ _).trans (eq_neg_of_add_eq_zero_left he.symm)

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem right_natDegree_eq_one_of_zero_direction (p₁ p₂ : Polynomial K) (c : ℕ) (a b : L)
    (h₁ : p₁ ≠ 0) (h₂ : p₂.Separable) (hs₂ : (p₂.map (algebraMap K L)).Splits)
    (hc : (c : L) = 0)
    (hinj : Set.InjOn (shear c) (rootPairs (L := L) p₁ p₂ : Set (L × L)))
    (ha : Polynomial.aeval a p₁ = 0) (hb : Polynomial.aeval b p₂ = 0) : p₂.natDegree = 1 := by
  classical
  let q := p₂.map (algebraMap K L)
  have hsep : q.Separable := h₂.map
  have hroot : q.eval b = 0 := by simpa only [q, Polynomial.eval_map_algebraMap] using hb
  have hlinear : q = C q.leadingCoeff * (X - C b) := by
    apply Polynomial.eq_X_sub_C_of_separable_of_root_eq (i := RingHom.id L) hsep hroot
    · simpa only [Polynomial.map_id] using hs₂
    · intro x hx
      have hxb : Polynomial.aeval x p₂ = 0 := by
        have hr := (Polynomial.mem_roots hsep.ne_zero).mp (by simpa only [Polynomial.map_id] using hx)
        simpa only [Polynomial.IsRoot, q, Polynomial.eval_map_algebraMap] using hr
      have hxpair := (mem_rootPairs p₁ p₂ h₁ h₂.ne_zero (a, x)).mpr ⟨ha, hxb⟩
      have hbpair := (mem_rootPairs p₁ p₂ h₁ h₂.ne_zero (a, b)).mpr ⟨ha, hb⟩
      exact congrArg Prod.snd (hinj hxpair hbpair (by simp only [shear, hc, zero_mul]))
  have hl : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hsep.ne_zero
  have hdeg : q.natDegree = 1 := by
    rw [hlinear, Polynomial.natDegree_C_mul hl, Polynomial.natDegree_X_sub_C]
  simpa only [q, Polynomial.natDegree_map] using hdeg

theorem coordinate_recovery_spec (p₁ p₂ : Polynomial K) (c : ℕ) (a b : L)
    (h₁ : p₁ ≠ 0) (h₂ : p₂.Separable) (hs₂ : (p₂.map (algebraMap K L)).Splits)
    (hinj : Set.InjOn (shear c) (rootPairs (L := L) p₁ p₂ : Set (L × L)))
    (ha : Polynomial.aeval a p₁ = 0) (hb : Polynomial.aeval b p₂ = 0) :
    let θ := shear c (a, b)
    let N := Polynomial.aeval θ (coordinateNumerator p₁ p₂ c)
    let D := Polynomial.aeval θ (coordinateDenominator p₁ p₂ c)
    D ≠ 0 ∧ b = -N / D ∧ a = θ + (c : L) * (N / D) := by
  classical
  let θ := shear c (a, b)
  suffices h : Polynomial.aeval θ (coordinateDenominator p₁ p₂ c) ≠ 0 ∧
      b = -Polynomial.aeval θ (coordinateNumerator p₁ p₂ c) /
        Polynomial.aeval θ (coordinateDenominator p₁ p₂ c) by
    dsimp only
    refine ⟨h.1, h.2, ?_⟩
    have hr : Polynomial.aeval θ (coordinateNumerator p₁ p₂ c) /
        Polynomial.aeval θ (coordinateDenominator p₁ p₂ c) = -b := by
      have he := h.2
      rw [neg_div] at he
      exact neg_eq_iff_eq_neg.mp he.symm
    rw [hr]
    dsimp [θ, shear]
    ring
  by_cases hn : p₂.natDegree = 1
  · have hdeg : (p₂.map (algebraMap K L)).natDegree = 1 := by rw [Polynomial.natDegree_map, hn]
    have he := linearPolynomial_root_spec (p₂.map (algebraMap K L)) b hdeg
      (by simpa only [Polynomial.eval_map_algebraMap] using hb)
    simpa only [coordinateNumerator, coordinateDenominator, hn, ↓reduceIte, Polynomial.aeval_C,
      Polynomial.coeff_map] using he
  · have hc : (c : L) ≠ 0 := fun h => hn
      (right_natDegree_eq_one_of_zero_direction p₁ p₂ c a b h₁ h₂ hs₂ h hinj ha hb)
    by_cases hm : p₁.natDegree = 1
    · have hdeg : (shiftedPolynomial p₁ c θ).natDegree = 1 := by rw [shiftedPolynomial_natDegree _ _ _ hc, hm]
      have hroot : (shiftedPolynomial p₁ c θ).eval b = 0 := by
        rw [eval_shiftedPolynomial]
        simpa only [θ, shear, add_sub_cancel_right] using ha
      have he := linearPolynomial_root_spec (shiftedPolynomial p₁ c θ) b hdeg hroot
      have hcoeff (r : ℕ) : Polynomial.aeval θ ((shiftFamily p₁ c).coeff r) =
          (shiftedPolynomial p₁ c θ).coeff r := by
        rw [← shiftFamily_specialize p₁ c θ, Polynomial.coeff_map]
        rfl
      simpa only [coordinateNumerator, coordinateDenominator, hn, hm, ↓reduceIte, hcoeff] using he
    · have hmp : 0 < p₁.natDegree := Polynomial.natDegree_pos_of_aeval_root h₁ ha
        (fun x hx => (algebraMap K L).injective (by simpa using hx))
      have hnp : 0 < p₂.natDegree := Polynomial.natDegree_pos_of_aeval_root h₂.ne_zero hb
        (fun x hx => (algebraMap K L).injective (by simpa using hx))
      have he := subresultant_recovery_spec p₁ p₂ c a b h₁ h₂ hs₂ (by omega) (by omega) hc hinj ha hb
      exact ⟨by simpa only [coordinateDenominator, hn, hm, ↓reduceIte] using he.1,
        by simpa only [coordinateNumerator, coordinateDenominator, hn, hm, ↓reduceIte] using he.2.1⟩

end LeanCanny.Algebra

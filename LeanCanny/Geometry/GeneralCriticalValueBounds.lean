/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.SystemCoordinateBounds
public import LeanCanny.Geometry.PolynomialCriticalValues
public import LeanCanny.Algebra.CriticalValueSystem
public import LeanCanny.Geometry.EffectiveRegularPolynomialLevels

/-! # Bounded critical-value annihilators for arbitrary integer polynomials

The critical-point locus may be singular or positive dimensional. Only its
value coordinate must have finite image. Applying the bounded finite-image
eliminant to the actual critical-value equations gives degree and mass bounds
from the source polynomial, and an explicit interval of regular positive levels.
-/

@[expose] public section
namespace LeanCanny.Geometry.GeneralCriticalValueBounds
open MvPolynomial Set LeanCanny.Algebra
open scoped Classical

variable {n : ℕ}

def massExponent (n D b : ℕ) : ℕ :=
  CoerciveRadiusBits.massExponent (n + 1) (2 * D) ((n + 1).size + 2 * (b + D.size + 1))

def exponent (n D b : ℕ) : ℕ := massExponent n D b + 1

noncomputable def level (n D b : ℕ) : ℝ := InfinitesimalSign.dyadic (exponent n D b)

theorem finite_value_image (p : MvPolynomial (Fin n) ℤ) :
    {t : ℝ | ∃ z : Fin (n + 1) → ℝ,
      (∀ j, (CriticalValueSystem.equations p j).eval₂ (Int.castRingHom ℝ) z = 0) ∧ z 0 = t}.Finite := by
  apply (CriticalValueAnnihilator.finite_critical_values (p.map (Int.castRingHom ℝ))).subset
  rintro t ⟨z, hz, ht⟩
  have hh := hz 0
  simp only [CriticalValueSystem.eval_equations, Fin.cons_zero, sub_eq_zero] at hh
  refine ⟨fun i => z i.succ, ?_, ?_⟩
  · intro i
    have hi := hz i.succ
    simpa only [CriticalValueSystem.eval_equations, Fin.cons_succ, aeval_def,
      Algebra.algebraMap_self, eval₂_id, pderiv_map, eval_map] using hi
  · simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, eval_map] using hh.symm.trans ht

theorem exists_bounded (p : MvPolynomial (Fin n) ℤ) (D b : ℕ) (hD : p.totalDegree ≤ D)
    (hpos : 0 < D) (hp : MvMass.mass p ≤ 2 ^ b) :
    ∃ q : Polynomial ℤ, q ≠ 0 ∧
      q.natDegree ≤ CoerciveCoordinateEliminant.columnBound (n + 1) (2 * D) ∧
      coefficientMass q < 2 ^ massExponent n D b ∧
      ∀ x : Fin n → ℝ, fderiv ℝ (fun y => p.eval₂ (Int.castRingHom ℝ) y) x = 0 →
        q.eval₂ (Int.castRingHom ℝ) (p.eval₂ (Int.castRingHom ℝ) x) = 0 := by
  have hd (j : Fin (n + 1)) : (CriticalValueSystem.equations p j).totalDegree ≤ D := by
    apply (CriticalValueSystem.degree_le p D hD hpos j).trans
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [CriticalValueSystem.degrees, Fin.cons_zero, le_refl]
    · simpa only [CriticalValueSystem.degrees, Fin.cons_succ] using Nat.sub_le D 1
  obtain ⟨q, hq, hdeg, hm, hann⟩ := SystemCoordinateBounds.exists_bounded
    (CriticalValueSystem.equations p) D (b + D.size + 1) hd
    (CriticalValueSystem.mass_bound p D b hD hp) 0 (finite_value_image p)
  refine ⟨q, hq, hdeg, hm, ?_⟩
  intro x hx
  exact hann (Fin.cons (p.eval₂ (Int.castRingHom ℝ) x) x)
    (CriticalValueSystem.critical_root (Int.castRingHom ℝ) p x
      ((PolynomialCalculus.critical_iff (Int.castRingHom ℝ) p x).mp hx))

theorem level_pos (n D b : ℕ) : 0 < level n D b := by
  unfold level InfinitesimalSign.dyadic
  positivity

theorem regular_interval (p : MvPolynomial (Fin n) ℤ) (D b : ℕ) (hD : p.totalDegree ≤ D)
    (hpos : 0 < D) (hp : MvMass.mass p ≤ 2 ^ b) (e : ℝ) (he : 0 < e) (heδ : e ≤ level n D b)
    (x : Fin n → ℝ) (hx : p.eval₂ (Int.castRingHom ℝ) x = e) :
    Function.Surjective (fderiv ℝ (fun y => p.eval₂ (Int.castRingHom ℝ) y) x) := by
  obtain ⟨q, hq, _hdeg, hmass, hann⟩ := exists_bounded p D b hD hpos hp
  apply RegularPolynomialLevels.surjective_of_ne_zero
  intro hz
  have ha := hann x hz
  rw [hx] at ha
  exact InfinitesimalSign.eval_ne_zero_le_dyadic q (massExponent n D b) hq hmass.le e he heδ ha

end LeanCanny.Geometry.GeneralCriticalValueBounds

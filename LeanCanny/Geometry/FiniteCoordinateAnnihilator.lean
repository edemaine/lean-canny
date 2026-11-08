/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CoerciveConstrainedSampling
public import LeanCanny.Geometry.CoerciveAnnihilatorLimit
public import LeanCanny.Algebra.CoerciveCoordinateEliminant
public import LeanCanny.Algebra.CoerciveRadiusBits

/-! # Bounded annihilators for finite projected zero sets

A finite coordinate image of an integer polynomial zero set has one nonzero
integer annihilator of bounded degree and coefficient mass. Singularities and
positive-dimensional spatial fibers are allowed. Constrained coercive samples
retain each isolated projected value before passing to the lowest coefficient
of a single critical-point eliminant.
-/

@[expose] public section
namespace LeanCanny.Geometry.FiniteCoordinateAnnihilator
open scoped Classical Topology
open Filter Set LeanCanny.Algebra
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- One lowest coefficient annihilates every projected zero when the coordinate
image is finite, irrespective of the dimensions of the spatial fibers. -/
theorem trailingCoeff_eval_eq_zero (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (i : Fin n) (H : Polynomial (Polynomial ℤ))
    (hann : CoerciveAnnihilatorLimit.IsCoordinateAnnihilator q D i H)
    (hfinite : {t : ℝ | ∃ x : Fin n → ℝ, MvPolynomial.eval x q = 0 ∧ x i = t}.Finite)
    (x0 : Fin n → ℝ) (hroot : MvPolynomial.eval x0 q = 0) :
    H.trailingCoeff.eval₂ (Int.castRingHom ℝ) (x0 i) = 0 := by
  obtain ⟨y, a, φ, hφ, hlim, hai, _hq, hc⟩ :=
    CoerciveConstrainedSampling.exists_critical_samples_at_coordinate q D i x0 hroot hfinite
  apply PolynomialLimitAnnihilator.trailingCoeff_eval_eq_zero_of_eventually H
    (fun k => 1 / ((φ k : ℝ) + 1)) (fun k => y (φ k) i) (x0 i)
  · intro k
    positivity
  · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  · rw [← hai]
    exact (continuous_apply i).continuousAt.tendsto.comp hlim
  · filter_upwards [hc] with k hk
    exact hann _ (by positivity) _ hk

/-- Degree and mass bounds are functions of the original polynomial. No
regularity, finite-fiber certificate, or supplied eliminant is assumed. -/
theorem exists_bounded (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n)
    (hfinite : {t : ℝ | ∃ x : Fin n → ℝ,
      q.eval₂ (Int.castRingHom ℝ) x = 0 ∧ x i = t}.Finite) :
    ∃ p : Polynomial ℤ, p ≠ 0 ∧
      p.natDegree ≤ CoerciveCoordinateEliminant.columnBound n D ∧
      coefficientMass p ≤ CoerciveCoordinateEliminant.massBound q D ∧
      ∀ x : Fin n → ℝ, q.eval₂ (Int.castRingHom ℝ) x = 0 →
        p.eval₂ (Int.castRingHom ℝ) (x i) = 0 := by
  obtain ⟨H, hH, _hs, ht, hm, hann⟩ :=
    CoerciveCoordinateEliminant.exists_annihilator q D hD i
  refine ⟨H.trailingCoeff, Polynomial.trailingCoeff_ne_zero.mpr hH,
    ht _, (NestedMass.coeff_le H H.natTrailingDegree).trans hm, ?_⟩
  intro x hx
  apply trailingCoeff_eval_eq_zero (q.map (Int.castRingHom ℝ)) D i H
    (fun s _hs y hy => hann s y hy)
  · simpa only [MvPolynomial.eval_map] using hfinite
  · simpa only [MvPolynomial.eval_map] using hx

/-- The mass allowance uses only dimension, degree, and the source mass
exponent. Its own binary length is bounded in `CoerciveRadiusBits`. -/
theorem exists_bounded_bits (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b) (i : Fin n)
    (hfinite : {t : ℝ | ∃ x : Fin n → ℝ,
      q.eval₂ (Int.castRingHom ℝ) x = 0 ∧ x i = t}.Finite) :
    ∃ p : Polynomial ℤ, p ≠ 0 ∧
      p.natDegree ≤ CoerciveCoordinateEliminant.columnBound n D ∧
      coefficientMass p < 2 ^ CoerciveRadiusBits.massExponent n D b ∧
      ∀ x : Fin n → ℝ, q.eval₂ (Int.castRingHom ℝ) x = 0 →
        p.eval₂ (Int.castRingHom ℝ) (x i) = 0 := by
  obtain ⟨p, hp, hd, hm, hann⟩ := exists_bounded q D hD i hfinite
  exact ⟨p, hp, hd, lt_of_lt_of_le (Nat.lt_succ_of_le hm)
    (CoerciveRadiusBits.massBound_add_one_le q D b hb), hann⟩

end LeanCanny.Geometry.FiniteCoordinateAnnihilator

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeProjection
public import LeanCanny.Geometry.LocalLevelApproximation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Every active zero point is approached by positive tube levels

At positive radius, scaling the shift vector by 1+t makes the radius equation
strictly positive for t>0. The tube energy is consequently positive along this
continuous path. Intermediate values give all sufficiently small positive
levels in any neighborhood of the original active zero point.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open scoped BigOperators

variable {ι : Type*}

def radialPath (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) (t : ℝ) : Coordinate ι → ℝ :=
  point (z.1, (1 + t) • z.2)

theorem radialPath_zero (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) : radialPath z 0 = point z := by
  simp [radialPath]

variable [Fintype ι]

omit [Fintype ι] in
theorem continuous_radialPath (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) : Continuous (radialPath z) := by
  apply continuous_pi
  intro i
  rcases i with j | j
  · change Continuous (fun _ : ℝ => z.1 j)
    exact continuous_const
  · change Continuous (fun t : ℝ => (1 + t) * z.2 j)
    exact (continuous_const.add continuous_id).mul continuous_const

theorem continuous_realEnergy (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) : Continuous (fun x : Coordinate ι → ℝ => MvPolynomial.aeval x (realEnergy p s epsilon delta)) :=
  (ProjectionCritical.contDiff_eval (algebraMap ℝ ℝ) (realEnergy p s epsilon delta)).continuous

theorem realEnergy_point (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) :
    MvPolynomial.aeval (point z) (realEnergy p s epsilon delta) =
      (SquaredRadius.value z.2 - delta ^ 2) ^ 2 +
        ∑ i ∈ s, PolynomialPerturbation.parameterMap p epsilon z i ^ 2 := by
  rw [eval_realEnergy, eval_energy]

theorem realEnergy_nonneg (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (x : Coordinate ι → ℝ) : 0 ≤ MvPolynomial.aeval x (realEnergy p s epsilon delta) := by
  rw [← point_splitPoint x, realEnergy_point]
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem radius_value_smul (c : ℝ) (a : PolynomialPerturbation.Constraint ι → ℝ) :
    SquaredRadius.value (c • a) = c ^ 2 * SquaredRadius.value a := by
  simp only [SquaredRadius.value, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem radial_energy_pos (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hd : 0 < delta) (hz : SquaredRadius.value z.2 = delta ^ 2) (t : ℝ) (ht : 0 < t) :
    0 < MvPolynomial.aeval (radialPath z t) (realEnergy p s epsilon delta) := by
  rw [radialPath, realEnergy_point]
  have hr : 0 < SquaredRadius.value ((1 + t) • z.2) - delta ^ 2 := by
    have he : SquaredRadius.value ((1 + t) • z.2) - delta ^ 2 = ((1 + t) ^ 2 - 1) * delta ^ 2 := by
      rw [radius_value_smul, hz]
      ring
    rw [he]
    exact mul_pos (by nlinarith [sq_nonneg t]) (sq_pos_of_pos hd)
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem recovery (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hd : 0 < delta) (hz : SquaredRadius.value z.2 = delta ^ 2)
    (ha : ∀ i ∈ s, PolynomialPerturbation.parameterMap p epsilon z i = 0) :
    LocalLevelApproximation.Recovery (fun x => MvPolynomial.aeval x (realEnergy p s epsilon delta)) (point z) := by
  have hsum : (∑ i ∈ s, PolynomialPerturbation.parameterMap p epsilon z i ^ 2) = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [ha i hi, zero_pow (by decide)])
  have hzero : MvPolynomial.aeval (point z) (realEnergy p s epsilon delta) = 0 := by
    simp only [realEnergy_point, hz, sub_self, zero_pow (by decide : 2 ≠ 0), hsum, add_zero]
  have h := LocalLevelApproximation.of_positive_path (fun x => MvPolynomial.aeval x (realEnergy p s epsilon delta))
    (continuous_realEnergy p s epsilon delta)
    (radialPath z) (continuous_radialPath z) (by rw [radialPath_zero]; exact hzero)
    (radial_energy_pos p s epsilon delta z hd hz)
  simpa only [radialPath_zero] using h

end LeanCanny.Geometry.TubePolynomial

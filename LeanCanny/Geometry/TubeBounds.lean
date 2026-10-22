/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubePolynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Uniform compact bounds for small tube samples

At tube levels at most one, shifts have magnitude at most delta+1. Nonnegative
inactive constraints and the active square bounds put every spatial coordinate
between -(delta+3) and delta+3 when epsilon and delta are nonnegative.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem level_energy_eq (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hz : (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) (point z) = 0) :
    (SquaredRadius.value z.2 - delta ^ 2) ^ 2 +
      (∑ i ∈ s, PolynomialPerturbation.parameterMap p epsilon z i ^ 2) = alpha := by
  rw [eval_polynomial, sub_eq_zero] at hz
  exact hz

theorem radius_square_le_level (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hz : (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) (point z) = 0) :
    (SquaredRadius.value z.2 - delta ^ 2) ^ 2 ≤ alpha := by
  have h := level_energy_eq p s epsilon delta alpha z hz
  have hn : 0 ≤ ∑ i ∈ s, PolynomialPerturbation.parameterMap p epsilon z i ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

theorem active_square_le_level (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hz : (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) (point z) = 0)
    (i : PolynomialPerturbation.Constraint ι) (hi : i ∈ s) :
    PolynomialPerturbation.parameterMap p epsilon z i ^ 2 ≤ alpha := by
  have h := level_energy_eq p s epsilon delta alpha z hz
  have ht := Finset.single_le_sum (f := fun j => PolynomialPerturbation.parameterMap p epsilon z j ^ 2)
    (fun _ _ => sq_nonneg _) hi
  nlinarith [sq_nonneg (SquaredRadius.value z.2 - delta ^ 2)]

theorem shift_bounds_level (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hd : 0 ≤ delta) (ha : alpha ≤ 1)
    (hz : (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) (point z) = 0)
    (i : PolynomialPerturbation.Constraint ι) : -(delta + 1) ≤ z.2 i ∧ z.2 i ≤ delta + 1 := by
  have hr : (SquaredRadius.value z.2 - delta ^ 2) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (radius_square_le_level p s epsilon delta alpha z hz).trans (by nlinarith)
  have hup := (abs_le_of_sq_le_sq' hr (by norm_num : (0 : ℝ) ≤ 1)).2
  have hi : z.2 i ^ 2 ≤ SquaredRadius.value z.2 :=
    Finset.single_le_sum (f := fun j => z.2 j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hs : z.2 i ^ 2 ≤ (delta + 1) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' hs (by linarith)

theorem constraint_lower_bound (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (ha : alpha ≤ 1) (hz : (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) (point z) = 0)
    (hinactive : ∀ i, i ∉ s → 0 ≤ PolynomialPerturbation.parameterMap p epsilon z i)
    (i : PolynomialPerturbation.Constraint ι) : -1 ≤ PolynomialPerturbation.parameterMap p epsilon z i := by
  classical
  by_cases hi : i ∈ s
  · have h : PolynomialPerturbation.parameterMap p epsilon z i ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (active_square_le_level p s epsilon delta alpha z hz i hi).trans (by nlinarith)
    exact (abs_le_of_sq_le_sq' h (by norm_num : (0 : ℝ) ≤ 1)).1
  · exact (by norm_num : (-1 : ℝ) ≤ 0).trans (hinactive i hi)

theorem spatial_bounds_level (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (he : 0 ≤ epsilon) (hd : 0 ≤ delta) (ha : alpha ≤ 1)
    (hz : (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) (point z) = 0)
    (hinactive : ∀ i, i ∉ s → 0 ≤ PolynomialPerturbation.parameterMap p epsilon z i) (i : ι) :
    -(delta + 3) ≤ z.1 i ∧ z.1 i ≤ delta + 3 := by
  have hlo := constraint_lower_bound p s epsilon delta alpha z ha hz hinactive (.inr (i, false))
  have hhi := constraint_lower_bound p s epsilon delta alpha z ha hz hinactive (.inr (i, true))
  have halo := (shift_bounds_level p s epsilon delta alpha z hd ha hz (.inr (i, false))).2
  have hahi := (shift_bounds_level p s epsilon delta alpha z hd ha hz (.inr (i, true))).2
  change -1 ≤ z.1 i + 1 - epsilon + z.2 (.inr (i, false)) at hlo
  change -1 ≤ 1 - epsilon - z.1 i + z.2 (.inr (i, true)) at hhi
  constructor <;> linarith

def sampleBox (ι : Type*) (delta : ℝ) : Set (Coordinate ι → ℝ) :=
  Set.Icc (fun _ => -(delta + 3)) (fun _ => delta + 3)

omit [Fintype ι] in
theorem isCompact_sampleBox (delta : ℝ) : IsCompact (sampleBox ι delta) := isCompact_Icc

theorem mem_sampleBox (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) (x : Coordinate ι → ℝ) (he : 0 ≤ epsilon) (hd : 0 ≤ delta) (ha : alpha ≤ 1)
    (hx : (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0)
    (hinactive : ∀ i, i ∉ s → 0 ≤ PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i) :
    x ∈ sampleBox ι delta := by
  have hz : (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) (point (splitPoint x)) = 0 := by
    simpa only [point_splitPoint] using hx
  have hb (i : Coordinate ι) : -(delta + 3) ≤ x i ∧ x i ≤ delta + 3 := by
    rcases i with i | i
    · exact spatial_bounds_level p s epsilon delta alpha (splitPoint x) he hd ha hz hinactive i
    · have h := shift_bounds_level p s epsilon delta alpha (splitPoint x) hd ha hz i
      change -(delta + 3) ≤ (splitPoint x).2 i ∧ (splitPoint x).2 i ≤ delta + 3
      constructor <;> linarith [h.1, h.2]
  exact ⟨fun i => (hb i).1, fun i => (hb i).2⟩

theorem mem_fixedBox (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) (x : Coordinate ι → ℝ) (he : 0 ≤ epsilon) (hd : 0 ≤ delta)
    (hd1 : delta ≤ 1) (ha : alpha ≤ 1)
    (hx : (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0)
    (hinactive : ∀ i, i ∉ s → 0 ≤ PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i) :
    x ∈ Set.Icc (fun _ => (-4 : ℝ)) (fun _ => (4 : ℝ)) := by
  have hb := mem_sampleBox p s epsilon delta alpha x he hd ha hx hinactive
  constructor
  · intro i
    have h : -(delta + 3) ≤ x i := hb.1 i
    linarith
  · intro i
    have h : x i ≤ delta + 3 := hb.2 i
    linarith

end LeanCanny.Geometry.TubePolynomial

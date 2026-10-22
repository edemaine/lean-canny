/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeBounds
public import LeanCanny.Geometry.TubeSigns

/-! # Feasibility from arbitrarily small tube samples

The active set may vary with the tube level. Square bounds give approximate
feasibility for all inequalities and both signs of the radius equation. A
uniform compact box then yields an exact feasible point.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open Set

variable {ι : Type*} [Fintype ι]

def Sample (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (alpha : ℝ) (x : Coordinate ι → ℝ) : Prop :=
  (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 ∧
    ∀ i, i ∉ s → 0 ≤ PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i

def PositiveSample (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (alpha : ℝ) (x : Coordinate ι → ℝ) : Prop :=
  (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 ∧
    ∀ i, i ∉ s → 0 < PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i

def SmallSamples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) : Prop :=
  ∀ b : ℝ, 0 < b → ∃ alpha : ℝ, 0 < alpha ∧ alpha < b ∧
    ∃ (s : Finset (PolynomialPerturbation.Constraint ι)) (x : Coordinate ι → ℝ), Sample p epsilon delta s alpha x

def EventualPositiveSamples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) : Prop :=
  ∃ s : Finset (PolynomialPerturbation.Constraint ι), ∃ b : ℝ, 0 < b ∧
    ∀ alpha : ℝ, 0 < alpha → alpha < b → ∃ x : Coordinate ι → ℝ, PositiveSample p epsilon delta s alpha x

noncomputable def approximationConstraint (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) :
    Sum Bool (PolynomialPerturbation.Constraint ι) → (Coordinate ι → ℝ) → ℝ
  | .inl false, x => SquaredRadius.value (splitPoint x).2 - delta ^ 2
  | .inl true, x => delta ^ 2 - SquaredRadius.value (splitPoint x).2
  | .inr i, x => PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i

theorem continuous_approximationConstraint (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (j : Sum Bool (PolynomialPerturbation.Constraint ι)) : Continuous (approximationConstraint p epsilon delta j) := by
  rcases j with b | i
  · have hc : Continuous (fun x : Coordinate ι → ℝ => SquaredRadius.value (splitPoint x).2) :=
      SquaredRadius.contDiff.continuous.comp (continuous_snd.comp continuous_splitPoint)
    cases b
    · exact hc.sub continuous_const
    · exact continuous_const.sub hc
  · exact (continuous_apply i).comp
      ((PolynomialPerturbation.contDiff_parameterMap p epsilon).continuous.comp continuous_splitPoint)

theorem approximationConstraint_iff (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) (x : Coordinate ι → ℝ) :
    (∀ j, 0 ≤ approximationConstraint p epsilon delta j x) ↔
      splitPoint x ∈ PolynomialPerturbation.perturbed p epsilon delta := by
  constructor
  · intro h
    have hp := h (.inl false)
    have hn := h (.inl true)
    change 0 ≤ SquaredRadius.value (splitPoint x).2 - delta ^ 2 at hp
    change 0 ≤ delta ^ 2 - SquaredRadius.value (splitPoint x).2 at hn
    exact ⟨fun i => h (.inr i), le_antisymm (sub_nonneg.mp hn) (sub_nonneg.mp hp)⟩
  · intro hx j
    rcases j with b | i
    · cases b <;> change 0 ≤ _ - _ <;> rw [show SquaredRadius.value (splitPoint x).2 = delta ^ 2 from hx.2, sub_self]
    · exact hx.1 i

theorem approximate_constraints (p : MvPolynomial ι ℤ) (epsilon delta alpha : ℝ)
    (s : Finset (PolynomialPerturbation.Constraint ι)) (x : Coordinate ι → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (ha : alpha ≤ b ^ 2) (hx : Sample p epsilon delta s alpha x) :
    ∀ j, -b ≤ approximationConstraint p epsilon delta j x := by
  classical
  have hz : (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) (point (splitPoint x)) = 0 := by
    simpa only [point_splitPoint] using hx.1
  have hr := abs_le_of_sq_le_sq' ((radius_square_le_level p s epsilon delta alpha (splitPoint x) hz).trans ha) hb
  intro j
  rcases j with c | i
  · cases c
    · exact hr.1
    · change -b ≤ delta ^ 2 - SquaredRadius.value (splitPoint x).2
      linarith [hr.2]
  · by_cases hi : i ∈ s
    · exact (abs_le_of_sq_le_sq'
        ((active_square_le_level p s epsilon delta alpha (splitPoint x) hz i hi).trans ha) hb).1
    · exact (neg_nonpos.mpr hb).trans (hx.2 i hi)

theorem feasible_of_small_samples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 ≤ delta) (h : SmallSamples p epsilon delta) :
    (PolynomialPerturbation.perturbed p epsilon delta).Nonempty := by
  have ha : ∀ b : ℝ, 0 < b → ∃ x ∈ sampleBox ι delta,
      ∀ j, -b ≤ approximationConstraint p epsilon delta j x := by
    intro b hb
    obtain ⟨alpha, hp, hs, s, x, hx⟩ := h (min (b ^ 2) 1) (lt_min (sq_pos_of_pos hb) (by norm_num))
    have h1 : alpha ≤ 1 := (lt_of_lt_of_le hs (min_le_right _ _)).le
    have hsq : alpha ≤ b ^ 2 := (lt_of_lt_of_le hs (min_le_left _ _)).le
    exact ⟨x, mem_sampleBox p s epsilon delta alpha x he hd h1 hx.1 hx.2,
      approximate_constraints p epsilon delta alpha s x b hb.le hsq hx⟩
  obtain ⟨x, _, hx⟩ := CompactApproximation.exists_feasible (sampleBox ι delta) (isCompact_sampleBox delta)
    (approximationConstraint p epsilon delta) (continuous_approximationConstraint p epsilon delta) ha
  exact ⟨splitPoint x, (approximationConstraint_iff p epsilon delta x).mp hx⟩

theorem eventual_positive_samples_of_feasible (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (hd : 0 < delta) (h : (PolynomialPerturbation.perturbed p epsilon delta).Nonempty) :
    EventualPositiveSamples p epsilon delta := by
  obtain ⟨z, hz⟩ := h
  let s := PolynomialPerturbation.activeSet p epsilon z
  have hactive : ∀ i ∈ s, PolynomialPerturbation.parameterMap p epsilon z i = 0 :=
    fun i hi => (PolynomialPerturbation.mem_activeSet p epsilon z i).mp hi
  let U : Set (Coordinate ι → ℝ) := {x | ∀ i, i ∉ s → 0 < PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i}
  have hU : U ∈ nhds (point z) := inactive_positive_near p s epsilon z
    (PolynomialPerturbation.inactive_pos p epsilon delta z hz)
  obtain ⟨b, hb, hr⟩ := recovery p s epsilon delta z hd hz.2 hactive U hU
  refine ⟨s, b, hb, ?_⟩
  intro alpha hp hs
  obtain ⟨x, hxU, hx⟩ := hr alpha hp hs
  refine ⟨x, ?_, hxU⟩
  rw [eval_as_realEnergy, sub_eq_zero]
  exact hx

theorem small_samples_of_eventual_positive (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (h : EventualPositiveSamples p epsilon delta) : SmallSamples p epsilon delta := by
  obtain ⟨s, a, ha, hs⟩ := h
  intro b hb
  obtain ⟨alpha, hp, hm⟩ := exists_between (lt_min ha hb)
  obtain ⟨x, hx⟩ := hs alpha hp (lt_of_lt_of_le hm (min_le_left _ _))
  exact ⟨alpha, hp, lt_of_lt_of_le hm (min_le_right _ _), s, x, hx.1, fun i hi => (hx.2 i hi).le⟩

theorem nonempty_iff_small_samples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) (he : 0 ≤ epsilon) (hd : 0 < delta) :
    (PolynomialPerturbation.perturbed p epsilon delta).Nonempty ↔ SmallSamples p epsilon delta :=
  ⟨fun h => small_samples_of_eventual_positive p epsilon delta (eventual_positive_samples_of_feasible p epsilon delta hd h),
    feasible_of_small_samples p epsilon delta he hd.le⟩

theorem nonempty_iff_eventual_positive_samples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) (he : 0 ≤ epsilon) (hd : 0 < delta) :
    (PolynomialPerturbation.perturbed p epsilon delta).Nonempty ↔ EventualPositiveSamples p epsilon delta :=
  ⟨eventual_positive_samples_of_feasible p epsilon delta hd,
    fun h => feasible_of_small_samples p epsilon delta he hd.le (small_samples_of_eventual_positive p epsilon delta h)⟩

end LeanCanny.Geometry.TubePolynomial

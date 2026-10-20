/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeCriticalMaximum
public import LeanCanny.Geometry.TubeProjectionFeasibility

/-! # Eventual projection samples from finite active critical sets

One normalized direction and one active set supply positive-inactive integer
projection roots at every sufficiently small tube level. This follows from
finiteness of the active critical sets and regularity of the active fibers.
Existence of a suitable direction and finiteness of the tube root sets are
separate obligations.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open Set

variable {ι : Type*} [Fintype ι]

def projectionRootSet (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) (v : Coordinate ι → ℝ) : Set (Coordinate ι → ℝ) :=
  {x | ∀ j, (integerProjection p s j).eval₂ (Int.castRingHom ℝ)
    (Sum.elim (Sum.elim x v) (parameters epsilon delta alpha)) = 0}

def EventualProjectionSamples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) (v : Coordinate ι → ℝ) : Prop :=
  ∃ s : Finset (PolynomialPerturbation.Constraint ι), ∃ b : ℝ, 0 < b ∧
    ∀ alpha : ℝ, 0 < alpha → alpha < b → ∃ x ∈ projectionRootSet p s epsilon delta alpha v,
      ∀ i, i ∉ s → 0 < PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i

def HasFiniteCriticalDirection (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) : Prop :=
  ∃ v : Coordinate ι → ℝ, v (base ι) = 1 ∧ FiniteActiveCriticalSets p epsilon delta v

theorem exists_regular_active_interval (p : MvPolynomial ι ℤ) (epsilon : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ delta : ℝ, 0 < delta → delta < d → RegularActiveFibers p epsilon delta :=
  PolynomialPerturbation.exists_regular_interval p epsilon

theorem eventual_projection_samples_of_approximation (p : MvPolynomial ι ℤ)
    (s : Finset (PolynomialPerturbation.Constraint ι)) (epsilon delta : ℝ) (v : Coordinate ι → ℝ)
    (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (h : CriticalApproximationWithPositiveInactive p s epsilon delta v z) :
    EventualProjectionSamples p epsilon delta v := by
  obtain ⟨b, hb, hs⟩ := h univ Filter.univ_mem
  refine ⟨s, b, hb, ?_⟩
  intro alpha hp ha
  obtain ⟨x, _, hi, _, _, hr⟩ := hs alpha hp ha
  exact ⟨x, hr, hi⟩

theorem small_projection_samples_of_eventual (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (v : Coordinate ι → ℝ) (h : EventualProjectionSamples p epsilon delta v) :
    SmallProjectionSamples p epsilon delta := by
  obtain ⟨s, a, ha, hr⟩ := h
  intro b hb
  obtain ⟨alpha, hp, hm⟩ := exists_between (lt_min ha hb)
  obtain ⟨x, hx, hi⟩ := hr alpha hp (lt_of_lt_of_le hm (min_le_left _ _))
  exact ⟨alpha, hp, lt_of_lt_of_le hm (min_le_right _ _), s, x, v, hx, fun i hi' => (hi i hi').le⟩

theorem eventual_projection_samples_of_finite_critical (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (v : Coordinate ι → ℝ) (he : 0 ≤ epsilon) (hd : 0 < delta)
    (hn : (PolynomialPerturbation.perturbed p epsilon delta).Nonempty)
    (hv : v (base ι) = 1) (hregular : RegularActiveFibers p epsilon delta)
    (hfinite : FiniteActiveCriticalSets p epsilon delta v) :
    EventualProjectionSamples p epsilon delta v := by
  obtain ⟨z, _, hz⟩ := exists_active_approximation p epsilon delta v he hd hn hv hregular hfinite
  exact eventual_projection_samples_of_approximation p _ epsilon delta v z hz

theorem nonempty_iff_eventual_projection_samples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (v : Coordinate ι → ℝ) (he : 0 ≤ epsilon) (hd : 0 < delta)
    (hv : v (base ι) = 1) (hregular : RegularActiveFibers p epsilon delta)
    (hfinite : FiniteActiveCriticalSets p epsilon delta v) :
    (PolynomialPerturbation.perturbed p epsilon delta).Nonempty ↔ EventualProjectionSamples p epsilon delta v :=
  ⟨fun hn => eventual_projection_samples_of_finite_critical p epsilon delta v he hd hn hv hregular hfinite,
    fun h => feasible_of_small_projection_samples p epsilon delta he hd.le
      (small_projection_samples_of_eventual p epsilon delta v h)⟩

theorem exists_eventual_projection_samples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 < delta)
    (hn : (PolynomialPerturbation.perturbed p epsilon delta).Nonempty)
    (hregular : RegularActiveFibers p epsilon delta) (hfinite : HasFiniteCriticalDirection p epsilon delta) :
    ∃ v : Coordinate ι → ℝ, v (base ι) = 1 ∧ EventualProjectionSamples p epsilon delta v := by
  obtain ⟨v, hv, hfin⟩ := hfinite
  exact ⟨v, hv, eventual_projection_samples_of_finite_critical p epsilon delta v he hd hn hv hregular hfin⟩

end LeanCanny.Geometry.TubePolynomial

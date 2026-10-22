/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CompactSupportingProjection
public import LeanCanny.Geometry.TubeCriticalSampling

/-! # Supporting projections give unconditional tube sampling completeness

A strict supporting projection of the compact perturbed set is strict on the
active zero locus near its maximum: inactive constraints remain positive.
Thus a fixed normalized direction and active set supply integer projection
roots with positive inactive signs at every sufficiently small tube level.
This is an existence theorem over the reals, not a finite sampling algorithm.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open Set Filter

variable {ι : Type*} [Fintype ι]

theorem active_strict_of_global_strict (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (v : Coordinate ι → ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hz : z ∈ PolynomialPerturbation.perturbed p epsilon delta)
    (hstrict : ∀ w ∈ PolynomialPerturbation.perturbed p epsilon delta, w ≠ z →
      splitProjection v w < splitProjection v z) :
    StrictLocalMaximum p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta v z := by
  let s := PolynomialPerturbation.activeSet p epsilon z
  have hnear := inactive_positive_near p s epsilon z (PolynomialPerturbation.inactive_pos p epsilon delta z hz)
  filter_upwards [hnear] with x hx hxzero hne
  obtain ⟨hr, ha⟩ := (mem_zeroLocus_iff p s epsilon delta x).mp hxzero
  have hfeasible : splitPoint x ∈ PolynomialPerturbation.perturbed p epsilon delta := by
    refine ⟨?_, hr⟩
    intro i
    change 0 ≤ PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i
    by_cases hi : i ∈ s
    · rw [ha i hi]
    · exact (hx i hi).le
  have hsplit : splitPoint x ≠ z := by
    intro heq
    exact hne ((point_splitPoint x).symm.trans (congrArg point heq))
  have h := hstrict (splitPoint x) hfeasible hsplit
  simpa only [splitProjection_apply, point_splitPoint] using h

theorem exists_strict_supporting_maximum (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 ≤ delta) (hn : (PolynomialPerturbation.perturbed p epsilon delta).Nonempty) :
    ∃ (v : Coordinate ι → ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)),
      z ∈ PolynomialPerturbation.perturbed p epsilon delta ∧ v (base ι) = 1 ∧
        StrictLocalMaximum p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta v z := by
  let K := point '' PolynomialPerturbation.perturbed p epsilon delta
  have hpoint : Continuous (point : ((ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) → Coordinate ι → ℝ) :=
    splitPointEquiv.symm.continuous
  have hK : IsCompact K := (PolynomialPerturbation.isCompact_perturbed p epsilon delta he hd).image hpoint
  obtain ⟨v, x, hx, hv, hm⟩ := CompactSupportingProjection.exists_strict_normalized K hK (hn.image point) (base ι)
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨v, z, hz, hv, active_strict_of_global_strict p epsilon delta v z hz ?_⟩
  intro w hw hne
  apply hm (point w) ⟨w, hw, rfl⟩
  intro heq
  exact hne (congrArg splitPoint heq)

theorem exists_eventual_projection_samples_of_feasible (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 < delta) (hn : (PolynomialPerturbation.perturbed p epsilon delta).Nonempty) :
    ∃ v : Coordinate ι → ℝ, v (base ι) = 1 ∧ EventualProjectionSamples p epsilon delta v := by
  obtain ⟨v, z, hz, hv, hstrict⟩ := exists_strict_supporting_maximum p epsilon delta he hd.le hn
  have hcrit := active_approximation_of_strict p epsilon delta v z hd hz hv hstrict
  exact ⟨v, hv, eventual_projection_samples_of_approximation p _ epsilon delta v z hcrit⟩

theorem nonempty_iff_exists_eventual_projection_samples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 < delta) :
    (PolynomialPerturbation.perturbed p epsilon delta).Nonempty ↔
      ∃ v : Coordinate ι → ℝ, v (base ι) = 1 ∧ EventualProjectionSamples p epsilon delta v := by
  constructor
  · exact exists_eventual_projection_samples_of_feasible p epsilon delta he hd
  · rintro ⟨v, _, hv⟩
    exact feasible_of_small_projection_samples p epsilon delta he hd.le
      (small_projection_samples_of_eventual p epsilon delta v hv)

theorem nonempty_iff_small_projection_samples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 < delta) :
    (PolynomialPerturbation.perturbed p epsilon delta).Nonempty ↔ SmallProjectionSamples p epsilon delta := by
  constructor
  · intro hn
    obtain ⟨v, _, hv⟩ := exists_eventual_projection_samples_of_feasible p epsilon delta he hd hn
    exact small_projection_samples_of_eventual p epsilon delta v hv
  · exact feasible_of_small_projection_samples p epsilon delta he hd.le

end LeanCanny.Geometry.TubePolynomial

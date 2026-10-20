/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeGenericDirections
public import LeanCanny.Geometry.TubeSupportingSampling
public import LeanCanny.Geometry.ProjectionContinuity
public import LeanCanny.Geometry.CompactLevelPerturbedMaxima

/-! # Finite tube root sets containing positive-inactive samples

Perturb a strict supporting direction to a nearby generic direction at each
small positive level. Uniform objective control keeps a local tube maximum
inside the positive-inactive neighborhood. Every active projection root set
is finite for the chosen direction. The direction may vary with the level;
no effective finite search or parameter bound is provided.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open Set Filter
open scoped Topology

variable {ι : Type*} [Fintype ι]

def EventualFiniteProjectionSamples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) : Prop :=
  ∃ s : Finset (PolynomialPerturbation.Constraint ι), ∃ a : ℝ, 0 < a ∧
    ∀ alpha : ℝ, 0 < alpha → alpha < a → ∃ v : Coordinate ι → ℝ, v (base ι) = 1 ∧
      (∀ t : Finset (PolynomialPerturbation.Constraint ι), (projectionRootSet p t epsilon delta alpha v).Finite) ∧
        ∃ x ∈ projectionRootSet p s epsilon delta alpha v,
          ∀ i, i ∉ s → 0 < PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i

def EventualFiniteProjectionSamplesWith (P : (Coordinate ι → ℝ) → Prop)
    (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) : Prop :=
  ∃ s : Finset (PolynomialPerturbation.Constraint ι), ∃ a : ℝ, 0 < a ∧
    ∀ alpha : ℝ, 0 < alpha → alpha < a → ∃ v : Coordinate ι → ℝ, v (base ι) = 1 ∧ P v ∧
      (∀ t : Finset (PolynomialPerturbation.Constraint ι), (projectionRootSet p t epsilon delta alpha v).Finite) ∧
        ∃ x ∈ projectionRootSet p s epsilon delta alpha v,
          ∀ i, i ∉ s → 0 < PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i

def NearbyFiniteProjectionDirections (P : (Coordinate ι → ℝ) → Prop)
    (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
    ∀ v : Coordinate ι → ℝ, v (base ι) = 1 →
      ∀ U : Set (Coordinate ι → ℝ), U ∈ nhds v →
        ∃ w ∈ U, w (base ι) = 1 ∧ P w ∧
          ∀ s : Finset (PolynomialPerturbation.Constraint ι), (projectionRootSet p s epsilon delta alpha w).Finite

theorem finite_samples_of_with (P : (Coordinate ι → ℝ) → Prop) (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (h : EventualFiniteProjectionSamplesWith P p epsilon delta) : EventualFiniteProjectionSamples p epsilon delta := by
  obtain ⟨s, a, ha, hr⟩ := h
  refine ⟨s, a, ha, ?_⟩
  intro alpha hp hs
  obtain ⟨v, hv, _, hfin, x, hx, hi⟩ := hr alpha hp hs
  exact ⟨v, hv, hfin, x, hx, hi⟩

theorem exists_sample_neighborhood_of_strict (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (v : Coordinate ι → ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hd : 0 < delta) (hz : z ∈ PolynomialPerturbation.perturbed p epsilon delta)
    (hstrict : StrictLocalMaximum p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta v z) :
    ∃ U : Set (Coordinate ι → ℝ), U ∈ nhds v ∧ ∃ a : ℝ, 0 < a ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < a → ∀ w ∈ U, w (base ι) = 1 →
        ∃ x ∈ projectionRootSet p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta alpha w,
          ∀ i, i ∉ PolynomialPerturbation.activeSet p epsilon z →
            0 < PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i := by
  let s := PolynomialPerturbation.activeSet p epsilon z
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hstrict
  let K := Metric.closedBall (point z) (r / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hpK : point z ∈ interior K := mem_interior_iff_mem_nhds.mpr
    (Metric.closedBall_mem_nhds _ (by linarith : 0 < r / 2))
  have hunique : UniqueMaximum p s epsilon delta v z K := by
    intro x hx hxzero hobj
    by_contra hne
    have hxball : x ∈ Metric.ball (point z) r := Metric.closedBall_subset_ball (by linarith) hx
    exact (not_lt_of_ge hobj) (hball hxball hxzero hne)
  let W : Set (Coordinate ι → ℝ) :=
    {x | ∀ i, i ∉ s → 0 < PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i}
  have hW : W ∈ nhds (point z) := inactive_positive_near p s epsilon z
    (PolynomialPerturbation.inactive_pos p epsilon delta z hz)
  have hactive : ∀ i ∈ s, PolynomialPerturbation.parameterMap p epsilon z i = 0 :=
    fun i hi => (PolynomialPerturbation.mem_activeSet p epsilon z i).mp hi
  obtain ⟨a, ha, e, he, hm⟩ := CompactLevelMaxima.exists_local_max_near_for_close_objectives K hK
    (fun x => MvPolynomial.aeval x (realEnergy p s epsilon delta)) (ProjectionCritical.projection v)
    (continuous_realEnergy p s epsilon delta) (ProjectionCritical.projection v).continuous (point z) hpK
    (fun x _ => realEnergy_nonneg p s epsilon delta x) hunique
    (recovery p s epsilon delta z hd hz.2 hactive) W hW
  let U : Set (Coordinate ι → ℝ) :=
    {w | ∀ x ∈ K, |ProjectionCritical.projection w x - ProjectionCritical.projection v x| < e}
  have hU : U ∈ nhds v := ProjectionCritical.close_on_compact K hK v e he
  obtain ⟨c, hc, hprojection⟩ := exists_integer_projection_interval p epsilon delta
  refine ⟨U, hU, min a c, lt_min ha hc, ?_⟩
  intro alpha hp hs w hwU hw
  have has : alpha < a := lt_of_lt_of_le hs (min_le_left _ _)
  have hcs : alpha < c := lt_of_lt_of_le hs (min_le_right _ _)
  obtain ⟨x, hxW, hlevel, hmax⟩ := hm alpha hp has (ProjectionCritical.projection w)
    (ProjectionCritical.projection w).continuous hwU
  have hx : (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 := by
    rw [eval_as_realEnergy, hlevel, sub_self]
  have hmaxTube : IsLocalMaxOn (ProjectionCritical.projection w)
      {y | (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) y = 0} x := by
    simpa only [eval_as_realEnergy, sub_eq_zero] using hmax
  exact ⟨x, hprojection alpha hp hcs s x w hw hx hmaxTube, hxW⟩

theorem eventual_finite_samples_of_strict_with (P : (Coordinate ι → ℝ) → Prop)
    (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (v : Coordinate ι → ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hd : 0 < delta) (hz : z ∈ PolynomialPerturbation.perturbed p epsilon delta)
    (hv : v (base ι) = 1)
    (hstrict : StrictLocalMaximum p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta v z)
    (hdirections : NearbyFiniteProjectionDirections P p epsilon delta) :
    EventualFiniteProjectionSamplesWith P p epsilon delta := by
  obtain ⟨U, hU, a, ha, hsamples⟩ := exists_sample_neighborhood_of_strict p epsilon delta v z hd hz hstrict
  obtain ⟨b, hb, hfinite⟩ := hdirections
  refine ⟨PolynomialPerturbation.activeSet p epsilon z, min a b, lt_min ha hb, ?_⟩
  intro alpha hp hs
  obtain ⟨w, hwU, hw, hP, hfin⟩ := hfinite alpha hp (hs.trans_le (min_le_right _ _)) v hv U hU
  exact ⟨w, hw, hP, hfin, hsamples alpha hp (hs.trans_le (min_le_left _ _)) w hwU hw⟩

theorem eventual_finite_samples_of_strict (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (v : Coordinate ι → ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hd : 0 < delta) (hz : z ∈ PolynomialPerturbation.perturbed p epsilon delta)
    (hv : v (base ι) = 1)
    (hstrict : StrictLocalMaximum p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta v z) :
    EventualFiniteProjectionSamples p epsilon delta := by
  have hdirs : NearbyFiniteProjectionDirections (fun _ => True) p epsilon delta := by
    obtain ⟨a, ha, hr⟩ := exists_finite_projection_directions_near p epsilon delta
    refine ⟨a, ha, ?_⟩
    intro alpha hp hs v hv U hU
    obtain ⟨w, hwU, hw, hfin⟩ := hr alpha hp hs v hv U hU
    exact ⟨w, hwU, hw, True.intro, hfin⟩
  exact finite_samples_of_with (fun _ => True) p epsilon delta
    (eventual_finite_samples_of_strict_with (fun _ => True) p epsilon delta v z hd hz hv hstrict hdirs)

theorem eventual_finite_samples_with_of_feasible (P : (Coordinate ι → ℝ) → Prop)
    (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 < delta) (hn : (PolynomialPerturbation.perturbed p epsilon delta).Nonempty)
    (hdirections : NearbyFiniteProjectionDirections P p epsilon delta) :
    EventualFiniteProjectionSamplesWith P p epsilon delta := by
  obtain ⟨v, z, hz, hv, hstrict⟩ := exists_strict_supporting_maximum p epsilon delta he hd.le hn
  exact eventual_finite_samples_of_strict_with P p epsilon delta v z hd hz hv hstrict hdirections

theorem eventual_finite_samples_of_feasible (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 < delta) (hn : (PolynomialPerturbation.perturbed p epsilon delta).Nonempty) :
    EventualFiniteProjectionSamples p epsilon delta := by
  obtain ⟨v, z, hz, hv, hstrict⟩ := exists_strict_supporting_maximum p epsilon delta he hd.le hn
  exact eventual_finite_samples_of_strict p epsilon delta v z hd hz hv hstrict

theorem small_projection_samples_of_eventual_finite (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (h : EventualFiniteProjectionSamples p epsilon delta) : SmallProjectionSamples p epsilon delta := by
  obtain ⟨s, a, ha, hr⟩ := h
  intro b hb
  obtain ⟨alpha, hp, hm⟩ := exists_between (lt_min ha hb)
  obtain ⟨v, _, _, x, hx, hi⟩ := hr alpha hp (lt_of_lt_of_le hm (min_le_left _ _))
  exact ⟨alpha, hp, lt_of_lt_of_le hm (min_le_right _ _), s, x, v, hx, fun i hn => (hi i hn).le⟩

theorem nonempty_iff_eventual_finite_samples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 < delta) :
    (PolynomialPerturbation.perturbed p epsilon delta).Nonempty ↔ EventualFiniteProjectionSamples p epsilon delta :=
  ⟨eventual_finite_samples_of_feasible p epsilon delta he hd,
    fun h => feasible_of_small_projection_samples p epsilon delta he hd.le
      (small_projection_samples_of_eventual_finite p epsilon delta h)⟩

end LeanCanny.Geometry.TubePolynomial

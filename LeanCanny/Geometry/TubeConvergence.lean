/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeApproximation
public import LeanCanny.Geometry.TubeExpanded
public import LeanCanny.Geometry.CompactLevelMaxima
public import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Compact tube limits and approximation of unique projection maxima

Vanishing tube levels have limits on the active zero locus and approach that
locus uniformly on compact sets. Near a unique zero-level projection maximum
in a compact neighborhood, every sufficiently small positive tube has a local
projection maximum satisfying the expanded integer critical equations.

Uniqueness is an explicit hypothesis. Generic directions yielding finite,
nondegenerate critical sets are not established by this theorem.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open Set Filter
open scoped Topology

variable {ι : Type*} [Fintype ι]

def zeroLocus (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) : Set (Coordinate ι → ℝ) :=
  {x | MvPolynomial.aeval x (realEnergy p s epsilon delta) = 0}

theorem mem_zeroLocus_iff (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (x : Coordinate ι → ℝ) :
    x ∈ zeroLocus p s epsilon delta ↔ SquaredRadius.value (splitPoint x).2 = delta ^ 2 ∧
      ∀ i ∈ s, PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i = 0 := by
  have h := zero_level_iff p s epsilon delta (splitPoint x)
  rw [point_splitPoint, eval_as_realEnergy, sub_zero] at h
  exact h

theorem small_tubes_in_open (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (K U : Set (Coordinate ι → ℝ)) (hK : IsCompact K) (hU : IsOpen U)
    (hzeros : ∀ x ∈ K, x ∈ zeroLocus p s epsilon delta → x ∈ U) :
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, alpha < a → ∀ x ∈ K,
      (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 → x ∈ U := by
  obtain ⟨a, ha, hm⟩ := CompactLevelConvergence.small_level_in_open K hK
    (fun x => MvPolynomial.aeval x (realEnergy p s epsilon delta)) (continuous_realEnergy p s epsilon delta)
    (fun x _ => realEnergy_nonneg p s epsilon delta x) U hU hzeros
  refine ⟨a, ha, ?_⟩
  intro alpha hs x hx hlevel
  rw [eval_as_realEnergy, sub_eq_zero] at hlevel
  apply hm x hx
  rw [hlevel]
  exact hs.le

theorem limit_mem_zeroLocus {A : Type*} {l : Filter A} [NeBot l]
    (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι)) (epsilon delta : ℝ)
    (x : A → Coordinate ι → ℝ) (alpha : A → ℝ) (q : Coordinate ι → ℝ)
    (hx : Tendsto x l (nhds q)) (ha : Tendsto alpha l (nhds 0))
    (hlevel : ∀ᶠ i in l, (polynomial p s).eval₂ (coefficientMap epsilon delta (alpha i)) (x i) = 0) :
    q ∈ zeroLocus p s epsilon delta := by
  have he : (fun i => MvPolynomial.aeval (x i) (realEnergy p s epsilon delta)) =ᶠ[l] alpha :=
    hlevel.mono fun i hi => by rw [eval_as_realEnergy, sub_eq_zero] at hi; exact hi
  have hzero := ha.congr' he.symm
  have hq := Filter.Tendsto.comp (continuous_realEnergy p s epsilon delta).continuousAt hx
  exact tendsto_nhds_unique hq hzero

def UniqueMaximum (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (v : Coordinate ι → ℝ)
    (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) (K : Set (Coordinate ι → ℝ)) : Prop :=
  ∀ x ∈ K, x ∈ zeroLocus p s epsilon delta →
    ProjectionCritical.projection v (point z) ≤ ProjectionCritical.projection v x → x = point z

def CriticalApproximation (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (v : Coordinate ι → ℝ)
    (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) : Prop :=
  ∀ U : Set (Coordinate ι → ℝ), U ∈ nhds (point z) →
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∃ x ∈ U, (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 ∧
        IsLocalMaxOn (ProjectionCritical.projection v)
          {y | (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) y = 0} x ∧
        ∀ j, (integerProjection p s j).eval₂ (Int.castRingHom ℝ)
          (Sum.elim (Sum.elim x v) (parameters epsilon delta alpha)) = 0

def StrictLocalMaximum (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (v : Coordinate ι → ℝ)
    (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) : Prop :=
  ∀ᶠ x in nhds (point z), x ∈ zeroLocus p s epsilon delta → x ≠ point z →
    ProjectionCritical.projection v x < ProjectionCritical.projection v (point z)

theorem critical_approximation (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (v : Coordinate ι → ℝ)
    (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hd : 0 < delta) (hz : SquaredRadius.value z.2 = delta ^ 2)
    (ha : ∀ i ∈ s, PolynomialPerturbation.parameterMap p epsilon z i = 0)
    (hv : v (base ι) = 1) (K : Set (Coordinate ι → ℝ)) (hK : IsCompact K)
    (hpK : point z ∈ interior K) (hunique : UniqueMaximum p s epsilon delta v z K) :
    CriticalApproximation p s epsilon delta v z := by
  intro U hU
  obtain ⟨a, ha, hm⟩ := CompactLevelMaxima.exists_local_max_near K hK
    (fun x => MvPolynomial.aeval x (realEnergy p s epsilon delta)) (ProjectionCritical.projection v)
    (continuous_realEnergy p s epsilon delta) (ProjectionCritical.projection v).continuous (point z) hpK
    (fun x _ => realEnergy_nonneg p s epsilon delta x) hunique
    (recovery p s epsilon delta z hd hz ha) U hU
  obtain ⟨b, hb, hr⟩ := exists_integer_projection_interval p epsilon delta
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro alpha hp hs
  obtain ⟨x, hxU, hlevel, hmax⟩ := hm alpha hp (lt_of_lt_of_le hs (min_le_left _ _))
  have hx : (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 := by
    rw [eval_as_realEnergy, hlevel, sub_self]
  have hmaxTube : IsLocalMaxOn (ProjectionCritical.projection v)
      {y | (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) y = 0} x := by
    simpa only [eval_as_realEnergy, sub_eq_zero] using hmax
  exact ⟨x, hxU, hx, hmaxTube, hr alpha hp (lt_of_lt_of_le hs (min_le_right _ _)) s x v hv hx hmaxTube⟩

theorem critical_approximation_of_strict (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (v : Coordinate ι → ℝ)
    (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hd : 0 < delta) (hz : SquaredRadius.value z.2 = delta ^ 2)
    (ha : ∀ i ∈ s, PolynomialPerturbation.parameterMap p epsilon z i = 0)
    (hv : v (base ι) = 1) (hstrict : StrictLocalMaximum p s epsilon delta v z) :
    CriticalApproximation p s epsilon delta v z := by
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
  exact critical_approximation p s epsilon delta v z hd hz ha hv K hK hpK hunique

end LeanCanny.Geometry.TubePolynomial

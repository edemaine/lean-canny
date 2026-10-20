/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeConvergence
public import LeanCanny.Geometry.PerturbedCriticalPoint

/-! # Positive inactive signs at approximating tube critical points

Continuity preserves all strictly positive inactive constraints in a common
neighborhood. The critical approximation theorem can use that neighborhood
while also respecting any prescribed neighborhood of the original point.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open Filter Set
open scoped Topology

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem splitPoint_point (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) : splitPoint (point z) = z := rfl

omit [Fintype ι] in
theorem continuous_splitPoint : Continuous (splitPoint : (Coordinate ι → ℝ) →
    (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) := by
  have hy : Continuous (fun x : Coordinate ι → ℝ => fun i : ι => x (.inl i)) :=
    continuous_pi (fun i : ι => continuous_apply (.inl i : Coordinate ι))
  have ha : Continuous (fun x : Coordinate ι → ℝ => fun i : PolynomialPerturbation.Constraint ι => x (.inr i)) :=
    continuous_pi (fun i : PolynomialPerturbation.Constraint ι => continuous_apply (.inr i : Coordinate ι))
  exact hy.prodMk ha

theorem inactive_positive_near (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon : ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hinactive : ∀ i, i ∉ s → 0 < PolynomialPerturbation.parameterMap p epsilon z i) :
    ∀ᶠ x in nhds (point z), ∀ i, i ∉ s → 0 < PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i := by
  classical
  apply Filter.eventually_all.mpr
  intro i
  by_cases hi : i ∈ s
  · exact Filter.Eventually.of_forall (fun _ hn => False.elim (hn hi))
  · have hc := (continuous_apply i).comp
      ((PolynomialPerturbation.contDiff_parameterMap p epsilon).continuous.comp continuous_splitPoint)
    have hp : 0 < PolynomialPerturbation.parameterMap p epsilon (splitPoint (point z)) i := by
      rw [splitPoint_point]
      exact hinactive i hi
    filter_upwards [hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hp)] with x hx
    exact fun _ => hx

def CriticalApproximationWithPositiveInactive (p : MvPolynomial ι ℤ)
    (s : Finset (PolynomialPerturbation.Constraint ι)) (epsilon delta : ℝ) (v : Coordinate ι → ℝ)
    (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) : Prop :=
  ∀ U : Set (Coordinate ι → ℝ), U ∈ nhds (point z) →
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∃ x ∈ U, (∀ i, i ∉ s → 0 < PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i) ∧
        (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 ∧
        IsLocalMaxOn (ProjectionCritical.projection v)
          {y | (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) y = 0} x ∧
        ∀ j, (integerProjection p s j).eval₂ (Int.castRingHom ℝ)
          (Sum.elim (Sum.elim x v) (parameters epsilon delta alpha)) = 0

theorem with_positive_inactive (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (v : Coordinate ι → ℝ)
    (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hcrit : CriticalApproximation p s epsilon delta v z)
    (hinactive : ∀ i, i ∉ s → 0 < PolynomialPerturbation.parameterMap p epsilon z i) :
    CriticalApproximationWithPositiveInactive p s epsilon delta v z := by
  intro U hU
  let W : Set (Coordinate ι → ℝ) := {x | ∀ i, i ∉ s → 0 < PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i}
  have hW : W ∈ nhds (point z) := inactive_positive_near p s epsilon z hinactive
  obtain ⟨a, ha, hr⟩ := hcrit (U ∩ W) (inter_mem hU hW)
  refine ⟨a, ha, ?_⟩
  intro alpha hp hs
  obtain ⟨x, hx, hlevel, hmax, heq⟩ := hr alpha hp hs
  exact ⟨x, hx.1, hx.2, hlevel, hmax, heq⟩

theorem limit_is_feasible {A : Type*} {l : Filter A} [NeBot l]
    (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι)) (epsilon delta : ℝ)
    (x : A → Coordinate ι → ℝ) (alpha : A → ℝ) (q : Coordinate ι → ℝ)
    (hx : Tendsto x l (nhds q)) (ha : Tendsto alpha l (nhds 0))
    (hlevel : ∀ᶠ a in l, (polynomial p s).eval₂ (coefficientMap epsilon delta (alpha a)) (x a) = 0)
    (hsigns : ∀ᶠ a in l, ∀ i, i ∉ s → 0 ≤ PolynomialPerturbation.parameterMap p epsilon (splitPoint (x a)) i) :
    splitPoint q ∈ PolynomialPerturbation.perturbed p epsilon delta := by
  obtain ⟨hr, hactive⟩ := (mem_zeroLocus_iff p s epsilon delta q).mp
    (limit_mem_zeroLocus p s epsilon delta x alpha q hx ha hlevel)
  refine ⟨?_, hr⟩
  intro i
  change 0 ≤ PolynomialPerturbation.parameterMap p epsilon (splitPoint q) i
  by_cases hi : i ∈ s
  · rw [hactive i hi]
  · have hc := (continuous_apply i).comp
      ((PolynomialPerturbation.contDiff_parameterMap p epsilon).continuous.comp continuous_splitPoint)
    exact isClosed_Ici.mem_of_tendsto (Filter.Tendsto.comp hc.continuousAt hx)
      (hsigns.mono fun a h => h i hi)

theorem active_approximation_of_strict (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (v : Coordinate ι → ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hd : 0 < delta) (hz : z ∈ PolynomialPerturbation.perturbed p epsilon delta)
    (hv : v (base ι) = 1)
    (hstrict : StrictLocalMaximum p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta v z) :
    CriticalApproximationWithPositiveInactive p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta v z := by
  have hactive : ∀ i ∈ PolynomialPerturbation.activeSet p epsilon z, PolynomialPerturbation.parameterMap p epsilon z i = 0 :=
    fun i hi => (PolynomialPerturbation.mem_activeSet p epsilon z i).mp hi
  have h := critical_approximation_of_strict p (PolynomialPerturbation.activeSet p epsilon z)
    epsilon delta v z hd hz.2 hactive hv hstrict
  exact with_positive_inactive p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta v z h
    (PolynomialPerturbation.inactive_pos p epsilon delta z hz)

end LeanCanny.Geometry.TubePolynomial

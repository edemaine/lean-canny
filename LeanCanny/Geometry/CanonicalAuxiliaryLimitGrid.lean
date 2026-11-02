/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateRealization

/-! # Actual selected relative limit factors meet each frozen clopen piece

The source is the single fixed-leading level lift with its causal capacity.
Every first nonzero eta factor is selected after the SAME old real hom. The
component point and all its free coordinates satisfy those actual factors;
no absolute norm-root lifting or assumed critical trajectory occurs.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory IntegralMixedCriticalSweep
open AuxiliaryTiltedTerm FrozenAuxiliaryComponentSampling IntegralMixedCanonicalDilation
open Set Filter Polynomial
open scoped Classical Topology
variable {n k D S B m G : ℕ} {t : Term} {ht : (term n t).degreeBound≤D} {ι : Type}

theorem meets_selected_factors (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (HG : x.bank.Bounds G) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (values : Fin m → ℝ) (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (ha : t.arity≤n) (hk : k≤n) (hD : 0<D) (select : Fin k → Fin m) (a : Fin n → ℝ)
    (Hparam : ∀ j : Fin n, ∀ hj : j.val<k, a j=values (select ⟨j.val,hj⟩))
    (C : Set (slice (polynomial n t) k a)) (hC : IsClopen C)
    (x0 : slice (polynomial n t) k a) (hx0 : x0∈C) :
    ∃ b : slice (polynomial n t) k a, b∈C ∧
      ∀ j : Fin (n+1), ∀ hj : k≤j.val,
      ∀ c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source k D t ht m B G) (rule (by omega : k≤n+1) select)),
        IntegralMixedLimitCoordinate.Valid x hm (rule (by omega : k≤n+1) select)
          (coordinateIndex (by omega : k≤n+1) select j hj) φ c →
        ((IntegralMixedLimitCoordinate.factor x hm (rule (by omega : k≤n+1) select)
          (coordinateIndex (by omega : k≤n+1) select j hj) c).map φ.toRingHom).eval
          ((Fin.snoc b.val 0 : Fin (n+1) → ℝ) j)=0 := by
  obtain ⟨y,b,eta,hb,hy,heta,hne,hr⟩ := exists_series_roots x hm HG φ values H ha hk hD select a Hparam C hC x0 hx0
  refine ⟨b,hb,?_⟩
  intro j hj c hc
  rw [IntegralMixedLimitCoordinate.selected_factor_eq x hm _ _ φ c hc]
  apply DeformationLowestCoefficient.trailingCoeff_eq_zero_of_tendsto _
    (fun z => evalRingHom z) (fun p => p.continuous) atTop (fun i => y i j) eta _
    (tendsto_pi_nhds.mp hy j) heta (Eventually.of_forall hne)
  filter_upwards [hr] with i hi
  exact hi j hj

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory

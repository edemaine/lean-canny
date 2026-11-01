/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FlatAffineExceptionalSelectedSections
public import LeanCanny.Connectivity.FlatAffineExceptionalSelectedRegularity
public import LeanCanny.Connectivity.FlatAffineRegularSlicePaths
/-! # Selected critical sections sample every full-slice path component off the height cuts -/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalSelectedPaths
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births)
open FlatAffineExceptionalOrderedRule (frozen order state rule sweep)
open FlatAffineExceptionalBankCorrelation (JointIndex MatchesFrame Correlated)
open FlatAffineExceptionalSelectedSlice (selectedSlice)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
  (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S)
  (hh : h u ∈ frozen F u) (r : Fin (arity F u)) (hr : r ∉ frozen F u)
  (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
  (z : JointIndex F u → ℝ) (HF : MatchesFrame F C h u v a hv z)
  (HG : Correlated F C h S u (hm.trans (Nat.le_succ S)) z)
  (φ : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
  (Hφ : ∀ i, φ ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.basis.generator i) =
    z (Sum.inl ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).sampler.scalar i)) ^
      UniformIntegralPowerSchedule.weights S (2 ^ FlatAffineExceptionalBankSource.width F u) (births F u) i)
  (hn : ∀ j i, FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i = 2 * FermatCoordinateCone.normal j i)

noncomputable def bad
    (c : IntegralMixedRelativeCuts.Choices (state F C h S u (hm.trans (Nat.le_succ S))) hm (sweep F C h S u hm hh r hr) φ) : Set ℝ :=
  IntegralMixedSelectedCriticalCuts.bad (state F C h S u (hm.trans (Nat.le_succ S))) hm (sweep F C h S u hm hh r hr) φ c ∪
    {t | (FlatAffineExceptionalCriticalHeight.cut F C h S u hm).eval₂ φ.toRingHom t = 0}

theorem finite_bad
    (c : IntegralMixedRelativeCuts.Choices (state F C h S u (hm.trans (Nat.le_succ S))) hm (sweep F C h S u hm hh r hr) φ) :
    (bad F C h S u hm hh r hr φ c).Finite :=
  (IntegralMixedSelectedCriticalCuts.finite_bad _ _ _ _ _).union (FlatAffineExceptionalCriticalHeight.finite_roots F C h S u hm φ)

include z HF HG Hφ hn in
theorem exists_sections
    (c : IntegralMixedRelativeCuts.Choices (state F C h S u (hm.trans (Nat.le_succ S))) hm (sweep F C h S u hm hh r hr) φ)
    (A B : ℝ) (t₀ : Ioo A B) (havoid : ∀ t ∈ Ioo A B, t ∉ bad F C h S u hm hh r hr φ c) :
    Finite (IntegralMixedSelectedPhysicalFiber.physical (state F C h S u (hm.trans (Nat.le_succ S))) hm
      (sweep F C h S u hm hh r hr) φ t₀.val) ∧
    ∃ curve : IntegralMixedSelectedPhysicalFiber.physical (state F C h S u (hm.trans (Nat.le_succ S))) hm
        (sweep F C h S u hm hh r hr) φ t₀.val → ℝ → Fin (arity F u) → ℝ,
      (∀ j, curve j t₀.val = j.val ∘ (order F u).symm) ∧
      (∀ j, ContinuousOn (curve j) (Icc A B)) ∧
      (∀ j t, t ∈ Icc A B → curve j t ∈ FlatAffineShiftedSlice.slice F u
        (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u) (FlatAffineExceptionalSliceFrame.scalar F C h u a+t)) ∧
      ∀ t : Ioo A B, ∀ y ∈ FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv)
        (h u) (FlatAffineExceptionalSliceFrame.scalar F C h u a+t.val),
        ∃ j, JoinedIn (FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)
          (FlatAffineExceptionalSliceFrame.scalar F C h u a+t.val)) y (curve j t.val) := by
  obtain ⟨Hfin,curve,HA,HC,HR,HS⟩ := FlatAffineExceptionalSelectedSections.exists_sections F C h S u v a hm hh r hr hv z HF HG φ Hφ hn c A B t₀
    (fun t ht Hbad => havoid t ht (Or.inl Hbad))
  have HV := FlatAffineExceptionalBankCorrelation.recovery_of_correlated F C h S u v a (hm.trans (Nat.le_succ S)) hv z HF HG φ Hφ
  refine ⟨Hfin,curve,HA,HC,HR,?_⟩
  intro t y hy
  obtain ⟨j,HJ⟩ := HS t y hy
  refine ⟨j,?_⟩
  apply FlatAffineRegularSlicePaths.joinedIn_of_component F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u) hh
    (FlatAffineExceptionalSliceFrame.scalar F C h u a+t.val) _ y hy (curve j t.val) HJ
  intro w hw
  exact FlatAffineExceptionalSelectedRegularity.regular_of_values F C h S u v a hm hh hv φ HV hn t.val
    (fun HZ => havoid t.val t.property (Or.inr HZ)) w hw

end LeanCanny.Connectivity.FlatAffineExceptionalSelectedPaths

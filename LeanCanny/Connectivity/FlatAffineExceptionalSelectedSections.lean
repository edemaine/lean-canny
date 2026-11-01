/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FlatAffineExceptionalSelectedSampling
/-! # Finite selected-parent critical sections meet all full-slice components -/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalSelectedSections
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

include z HF HG Hφ hn in
theorem exists_sections
    (c : IntegralMixedRelativeCuts.Choices (state F C h S u (hm.trans (Nat.le_succ S))) hm (sweep F C h S u hm hh r hr) φ)
    (A B : ℝ) (t₀ : Ioo A B)
    (havoid : ∀ t ∈ Ioo A B, t ∉ IntegralMixedSelectedCriticalCuts.bad
      (state F C h S u (hm.trans (Nat.le_succ S))) hm (sweep F C h S u hm hh r hr) φ c) :
    Finite (IntegralMixedSelectedPhysicalFiber.physical (state F C h S u (hm.trans (Nat.le_succ S))) hm
      (sweep F C h S u hm hh r hr) φ t₀.val) ∧
    ∃ curve : IntegralMixedSelectedPhysicalFiber.physical (state F C h S u (hm.trans (Nat.le_succ S))) hm
        (sweep F C h S u hm hh r hr) φ t₀.val → ℝ → Fin (arity F u) → ℝ,
      (∀ j, curve j t₀.val = j.val ∘ (order F u).symm) ∧
      (∀ j, ContinuousOn (curve j) (Icc A B)) ∧
      (∀ j t, t ∈ Icc A B → curve j t ∈ FlatAffineShiftedSlice.slice F u
        (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u) (FlatAffineExceptionalSliceFrame.scalar F C h u a + t)) ∧
      ∀ t : Ioo A B, ∀ y ∈ FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv)
        (h u) (FlatAffineExceptionalSliceFrame.scalar F C h u a + t.val),
        ∃ j, curve j t.val ∈ connectedComponentIn
          (FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)
            (FlatAffineExceptionalSliceFrame.scalar F C h u a + t.val)) y := by
  obtain ⟨Hfin,curve,HA,HC,HR,HE,_⟩ := IntegralMixedSelectedPhysicalArcs.anchored_physical_arcs
    (state F C h S u (hm.trans (Nat.le_succ S))) hm (sweep F C h S u hm hh r hr) φ c A B t₀ havoid
  refine ⟨Hfin,fun j t => curve j t ∘ (order F u).symm,?_,?_,?_,?_⟩
  · intro j
    exact congrArg (fun y => y ∘ (order F u).symm) (HA j)
  · intro j
    exact (continuous_pi (fun i => continuous_apply ((order F u).symm i))).comp_continuousOn (HC j)
  · intro j t ht
    exact FlatAffineExceptionalSelectedHomeomorph.critical_mem_slice F C h S u v a hm hh r hr hv z HF HG φ Hφ hn t (curve j t) (HR j t ht)
  · intro t y hy
    obtain ⟨w,HW,HS⟩ := FlatAffineExceptionalSelectedSampling.sample_component F C h S u v a hm hh r hr hv z HF HG φ Hφ hn t.val y hy
    obtain ⟨j,HJ,_⟩ := (HE t w).mp HW
    refine ⟨j,?_⟩
    change (curve j t.val ∘ (order F u).symm) ∈ _
    rw [HJ]
    exact HS

end LeanCanny.Connectivity.FlatAffineExceptionalSelectedSections

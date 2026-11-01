/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FlatAffineExceptionalSelectedHomeomorph
public import LeanCanny.Connectivity.IntegralMixedSelectedComponentSampling
/-! # Exact selected critical sections meet every exceptional slice component -/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalSelectedSampling
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
theorem selected_compact (t : ℝ) : IsCompact (selectedSlice F C h S u hm hh r hr φ t) := by
  let E := FlatAffineExceptionalSelectedHomeomorph.homeomorph F C h S u v a hm hh r hr hv z HF HG φ Hφ hn t
  let : CompactSpace (FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)
      (FlatAffineExceptionalSliceFrame.scalar F C h u a + t)) :=
    isCompact_iff_compactSpace.mp (FlatAffineShiftedSlice.compact F u _ _ _)
  exact isCompact_iff_compactSpace.mpr E.symm.compactSpace

include z HF HG Hφ hn in
theorem sample_component (t : ℝ) (y : Fin (arity F u) → ℝ)
    (hy : y ∈ FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)
      (FlatAffineExceptionalSliceFrame.scalar F C h u a + t)) :
    ∃ w : Fin (arity F u) → ℝ,
      w ∈ IntegralMixedSelectedPhysicalFiber.physical (state F C h S u (hm.trans (Nat.le_succ S))) hm
        (sweep F C h S u hm hh r hr) φ t ∧
      (w ∘ (order F u).symm) ∈ connectedComponentIn
        (FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)
          (FlatAffineExceptionalSliceFrame.scalar F C h u a + t)) y := by
  let X := state F C h S u (hm.trans (Nat.le_succ S))
  let R := sweep F C h S u hm hh r hr
  let U := IntegralMixedSelectedComponentSampling.fiber X hm R φ t
  let f : (Fin (arity F u) → ℝ) → (Fin (arity F u) → ℝ) := fun w => w ∘ (order F u).symm
  have HE : U = selectedSlice F C h S u hm hh r hr φ t := rfl
  have HC : IsCompact U := HE ▸ selected_compact F C h S u v a hm hh r hr hv z HF HG φ Hφ hn t
  have HY : (y ∘ order F u) ∈ U := by
    rw [HE]
    apply (FlatAffineExceptionalSelectedSlice.slice_iff_correlated F C h S u v a hm hh r hr hv z HF HG φ Hφ hn t _).mpr
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using hy
  obtain ⟨w,HW,HP⟩ := IntegralMixedSelectedComponentSampling.exists_component_critical X hm R φ t HC (y ∘ order F u) HY
  have HFcont : Continuous f := continuous_pi (fun i => continuous_apply ((order F u).symm i))
  have Hpre : IsPreconnected (f '' connectedComponentIn U (y ∘ order F u)) :=
    isPreconnected_connectedComponentIn.image _ HFcont.continuousOn
  have Hbase : y ∈ f '' connectedComponentIn U (y ∘ order F u) := by
    refine ⟨y ∘ order F u, mem_connectedComponentIn HY, ?_⟩
    funext i
    simp only [f, Function.comp_apply, Equiv.apply_symm_apply]
  have Hsub : f '' connectedComponentIn U (y ∘ order F u) ⊆
      FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)
        (FlatAffineExceptionalSliceFrame.scalar F C h u a + t) := by
    rintro _ ⟨w,HW,rfl⟩
    exact (FlatAffineExceptionalSelectedSlice.slice_iff_correlated F C h S u v a hm hh r hr hv z HF HG φ Hφ hn t w).mp
      (HE ▸ connectedComponentIn_subset U _ HW)
  exact ⟨w,HP,Hpre.subset_connectedComponentIn Hbase Hsub ⟨w,HW,rfl⟩⟩

end LeanCanny.Connectivity.FlatAffineExceptionalSelectedSampling

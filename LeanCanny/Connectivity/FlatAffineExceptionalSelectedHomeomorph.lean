/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FlatAffineExceptionalSelectedSlice
/-! # Exact exceptional-frame homeomorphisms and selected critical sections -/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalSelectedHomeomorph
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births)
open FlatAffineExceptionalOrderedRule (frozen order state rule sweep)
open FlatAffineExceptionalBankCorrelation (JointIndex MatchesFrame Correlated)
open FlatAffineExceptionalSelectedSlice (selectedSlice)
open IntegralMixedHistory IntegralMixedCriticalSweep
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

noncomputable def homeomorph (t : ℝ) :
    selectedSlice F C h S u hm hh r hr φ t ≃ₜ
      FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)
        (FlatAffineExceptionalSliceFrame.scalar F C h u a + t) where
  toFun y := ⟨y.val ∘ (order F u).symm,
    (FlatAffineExceptionalSelectedSlice.slice_iff_correlated F C h S u v a hm hh r hr hv z HF HG φ Hφ hn t y.val).mp y.property⟩
  invFun y := ⟨y.val ∘ (order F u), (FlatAffineExceptionalSelectedSlice.slice_iff_correlated F C h S u v a hm hh r hr hv z HF HG φ Hφ hn t _).mpr (by
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using y.property)⟩
  left_inv y := by apply Subtype.ext; funext i; simp only [Function.comp_apply, Equiv.symm_apply_apply]
  right_inv y := by apply Subtype.ext; funext i; simp only [Function.comp_apply, Equiv.apply_symm_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_apply ((order F u).symm i)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_apply (order F u i)).comp continuous_subtype_val

noncomputable def endpointHomeomorph : selectedSlice F C h S u hm hh r hr φ 0 ≃ₜ
    FlatAffineExceptionalSliceFrame.slice F C h u v a hv :=
  (homeomorph F C h S u v a hm hh r hr hv z HF HG φ Hφ hn 0).trans
    (Homeomorph.setCongr (by rw [add_zero]; exact (FlatAffineExceptionalSliceFrame.slice_eq F C h u v a hv).symm))

noncomputable def endpointCover {J : Type} (cover : ClopenPathCover (selectedSlice F C h S u hm hh r hr φ 0) J) :
    ClopenPathCover (FlatAffineExceptionalSliceFrame.slice F C h u v a hv) J :=
  cover.comap (endpointHomeomorph F C h S u v a hm hh r hr hv z HF HG φ Hφ hn).symm

include z HF HG Hφ hn in
theorem critical_mem_slice (t : ℝ) (y : Fin (arity F u) → ℝ)
    (hy : y ∈ IntegralMixedSelectedPhysicalFiber.physical
      (state F C h S u (hm.trans (Nat.le_succ S))) hm (sweep F C h S u hm hh r hr) φ t) :
    (y ∘ (order F u).symm) ∈ FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv)
      (h u) (FlatAffineExceptionalSliceFrame.scalar F C h u a + t) := by
  apply (FlatAffineExceptionalSelectedSlice.slice_iff_correlated F C h S u v a hm hh r hr hv z HF HG φ Hφ hn t y).mp
  exact ⟨IntegralMixedSelectedCoordinateStatus.source_zero _ hm _ φ t y hy, hy.1⟩

end LeanCanny.Connectivity.FlatAffineExceptionalSelectedHomeomorph

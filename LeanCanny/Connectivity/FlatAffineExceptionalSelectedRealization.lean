/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FlatAffineExceptionalSelectedHomeomorph
/-! # Valid independent frame labels construct one correlated hom for every sweep fiber -/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalSelectedRealization
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births)
open FlatAffineExceptionalOrderedRule (frozen order state)
open FlatAffineExceptionalBankCorrelation (JointIndex MatchesFrame Correlated)
open FlatAffineExceptionalSelectedSlice (selectedSlice)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem exists_correlated_slices (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S)
    (hh : h u ∈ frozen F u) (r : Fin (arity F u)) (hr : r ∉ frozen F u)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a)
    (hn : ∀ j i, FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i = 2 * FermatCoordinateCone.normal j i) :
    ∃ z : JointIndex F u → ℝ,
      ∃ φ : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
      MatchesFrame F C h u v a hv z ∧ Correlated F C h S u (hm.trans (Nat.le_succ S)) z ∧
      (∀ i, φ ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.basis.generator i) =
        z (Sum.inl ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).sampler.scalar i)) ^
          UniformIntegralPowerSchedule.weights S (2 ^ FlatAffineExceptionalBankSource.width F u) (births F u) i) ∧
      (∀ t : ℝ, Nonempty (selectedSlice F C h S u hm hh r hr φ t ≃ₜ
        FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)
          (FlatAffineExceptionalSliceFrame.scalar F C h u a + t))) ∧
      Nonempty (selectedSlice F C h S u hm hh r hr φ 0 ≃ₜ FlatAffineExceptionalSliceFrame.slice F C h u v a hv) := by
  obtain ⟨z,φ,_,HF,HG,Hφ⟩ := FlatAffineExceptionalBankCorrelation.exists_correlated_realization F C h S u v a
    (hm.trans (Nat.le_succ S)) hv ha
  exact ⟨z,φ,HF,HG,Hφ,
    fun t => ⟨FlatAffineExceptionalSelectedHomeomorph.homeomorph F C h S u v a hm hh r hr hv z HF HG φ Hφ hn t⟩,
    ⟨FlatAffineExceptionalSelectedHomeomorph.endpointHomeomorph F C h S u v a hm hh r hr hv z HF HG φ Hφ hn⟩⟩

end LeanCanny.Connectivity.FlatAffineExceptionalSelectedRealization

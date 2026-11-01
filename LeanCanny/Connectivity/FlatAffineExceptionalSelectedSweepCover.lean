/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FlatAffineExceptionalSelectedCover
public import LeanCanny.Connectivity.FiniteSlabCover
/-! # Assembling every selected-parent slab into the full coarse-slice cover -/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalSelectedSweepCover
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births)
open FlatAffineExceptionalOrderedRule (frozen order state rule sweep)
open FlatAffineExceptionalBankCorrelation (JointIndex MatchesFrame Correlated)
open FlatAffineExceptionalSelectedSlice (selectedSlice)
open FlatAffineShiftedSlice (projection)
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


variable {k : ℕ} (cut : ℕ → ℝ)
  (hc : StrictMonoOn cut (Icc 0 (k+1)))

noncomputable def sample (i : Fin (k+1)) : Ioo (cut i.val) (cut (i.val+1)) :=
  ⟨(cut i.val+cut (i.val+1))/2, by
    have H := hc ⟨Nat.zero_le _,Nat.le_of_lt i.isLt⟩
      ⟨Nat.zero_le _,Nat.succ_le_of_lt i.isLt⟩ (Nat.lt_succ_self _)
    constructor <;> linarith⟩

abbrev SlabIndex (E : Fin (k+2) → Type) (i : Fin (k+1)) :=
  ComponentSlabCover.SelectedIndex
    (IntegralMixedSelectedPhysicalFiber.physical (state F C h S u (hm.trans (Nat.le_succ S))) hm
      (sweep F C h S u hm hh r hr) φ (sample cut hc i).val)
    (E i.castSucc) (E i.succ)

include z HF HG Hφ hn in
theorem exists_local_covers
    (c : IntegralMixedRelativeCuts.Choices (state F C h S u (hm.trans (Nat.le_succ S))) hm (sweep F C h S u hm hh r hr) φ)
    (ha : ∀ i : Fin (k+1), ∀ t ∈ Ioo (cut i.val) (cut (i.val+1)),
      t ∉ FlatAffineExceptionalSelectedPaths.bad F C h S u hm hh r hr φ c)
    (E : Fin (k+2) → Type) [∀ j, Finite (E j)]
    (ends : ∀ j : Fin (k+2), ClopenPathCover
      ((projection F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)) ⁻¹'
        {FlatAffineExceptionalSliceFrame.scalar F C h u a+cut j.val}) (E j)) :
    ∀ i : Fin (k+1), Finite (SlabIndex F C h S u hm hh r hr φ cut hc E i) ∧
      Nonempty (ClopenPathCover
        ((projection F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)) ⁻¹'
          Icc (FlatAffineExceptionalSliceFrame.scalar F C h u a+cut i.val)
            (FlatAffineExceptionalSliceFrame.scalar F C h u a+cut (i.val+1)))
        (SlabIndex F C h S u hm hh r hr φ cut hc E i)) := by
  intro i
  obtain ⟨Hfin,_,_⟩ := FlatAffineExceptionalSelectedSaturation.exists_interior_data
    F C h S u v a hm hh r hr hv z HF HG φ Hφ hn c (cut i.val) (cut (i.val+1)) (sample cut hc i) (ha i)
  let : Finite (IntegralMixedSelectedPhysicalFiber.physical (state F C h S u (hm.trans (Nat.le_succ S))) hm
    (sweep F C h S u hm hh r hr) φ (sample cut hc i).val) := Hfin
  exact ⟨inferInstance,FlatAffineExceptionalSelectedCover.exists_component_cover
    F C h S u v a hm hh r hr hv z HF HG φ Hφ hn c (cut i.val) (cut (i.val+1)) (sample cut hc i) (ha i)
    (ends i.castSucc) (ends i.succ)⟩

include z HF HG Hφ hn in
theorem exists_component_cover
    (c : IntegralMixedRelativeCuts.Choices (state F C h S u (hm.trans (Nat.le_succ S))) hm (sweep F C h S u hm hh r hr) φ)
    (ha : ∀ i : Fin (k+1), ∀ t ∈ Ioo (cut i.val) (cut (i.val+1)),
      t ∉ FlatAffineExceptionalSelectedPaths.bad F C h S u hm hh r hr φ c)
    (E : Fin (k+2) → Type) [∀ j, Finite (E j)]
    (ends : ∀ j : Fin (k+2), ClopenPathCover
      ((projection F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)) ⁻¹'
        {FlatAffineExceptionalSliceFrame.scalar F C h u a+cut j.val}) (E j))
    (hb : ∀ y, projection F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u) y ∈
      Icc (FlatAffineExceptionalSliceFrame.scalar F C h u a+cut 0)
        (FlatAffineExceptionalSliceFrame.scalar F C h u a+cut (k+1))) :
    Finite (Σ i : Fin (k+1), SlabIndex F C h S u hm hh r hr φ cut hc E i) ∧
      Nonempty (ClopenPathCover
        (FlatAffineShiftedSlice.coarseSlice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u))
        (Σ i : Fin (k+1), SlabIndex F C h S u hm hh r hr φ cut hc E i)) := by
  have Hloc := exists_local_covers F C h S u v a hm hh r hr hv z HF HG φ Hφ hn cut hc c ha E ends
  let : ∀ i : Fin (k+1), Finite (SlabIndex F C h S u hm hh r hr φ cut hc E i) := fun i => (Hloc i).1
  let D := fun i => (Hloc i).2.some
  have HP := (FlatAffineShiftedSlice.projection_proper F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)).continuous
  exact ⟨inferInstance,⟨FiniteSlabCover.componentCover _
    (fun j => FlatAffineExceptionalSliceFrame.scalar F C h u a+cut j) D HP hb⟩⟩

end LeanCanny.Connectivity.FlatAffineExceptionalSelectedSweepCover

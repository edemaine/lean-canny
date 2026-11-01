/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FlatAffineExceptionalSelectedSaturation
/-! # Recursive endpoint covers for the full selected-parent exceptional slab -/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalSelectedCover
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

include z HF HG Hφ hn in
theorem exists_component_cover {L R : Type*} [Finite L] [Finite R]
    (c : IntegralMixedRelativeCuts.Choices (state F C h S u (hm.trans (Nat.le_succ S))) hm (sweep F C h S u hm hh r hr) φ)
    (A B : ℝ) (t₀ : Ioo A B)
    (havoid : ∀ t ∈ Ioo A B, t ∉ FlatAffineExceptionalSelectedPaths.bad F C h S u hm hh r hr φ c)
    (left : ClopenPathCover ((projection F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)) ⁻¹'
      {FlatAffineExceptionalSliceFrame.scalar F C h u a+A}) L)
    (right : ClopenPathCover ((projection F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)) ⁻¹'
      {FlatAffineExceptionalSliceFrame.scalar F C h u a+B}) R) :
    Nonempty (ClopenPathCover ((projection F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)) ⁻¹'
      Icc (FlatAffineExceptionalSliceFrame.scalar F C h u a+A) (FlatAffineExceptionalSliceFrame.scalar F C h u a+B))
      (ComponentSlabCover.SelectedIndex
        (IntegralMixedSelectedPhysicalFiber.physical (state F C h S u (hm.trans (Nat.le_succ S))) hm
          (sweep F C h S u hm hh r hr) φ t₀.val) L R)) := by
  let α := FlatAffineExceptionalSliceFrame.scalar F C h u a
  obtain ⟨Hfin,D,_,_,_⟩ := FlatAffineExceptionalSelectedSaturation.exists_interior_data
    F C h S u v a hm hh r hr hv z HF HG φ Hφ hn c A B t₀ havoid
  let : Finite (IntegralMixedSelectedPhysicalFiber.physical (state F C h S u (hm.trans (Nat.le_succ S))) hm
    (sweep F C h S u hm hh r hr) φ t₀.val) := Hfin
  obtain ⟨l,r,HS⟩ := ComponentSlabCover.exists_selection D left right
  have HP := (FlatAffineShiftedSlice.projection_proper F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)).continuous
  have HAB : α+A < α+B := by linarith [t₀.property.1,t₀.property.2]
  let anchor : Ioo (α+A) (α+B) := ⟨α+t₀.val,by constructor <;> linarith [t₀.property.1,t₀.property.2]⟩
  exact ⟨ClopenPathCover.ofClosed (ComponentSlabCover.selectedPiece D left right l r)
    (ComponentSlabCover.selected_closed D left right l r HP)
    (ComponentSlabCover.selected_cover D left right l r HS)
    (ComponentSlabCover.selected_paths D left right l r HP HAB anchor)⟩

end LeanCanny.Connectivity.FlatAffineExceptionalSelectedCover

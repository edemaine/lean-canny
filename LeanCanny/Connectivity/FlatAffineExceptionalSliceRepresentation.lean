/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalSliceFrame
public import LeanCanny.Connectivity.ClopenPathCover

/-! # All exceptional endpoint fibers have independent parameter frames

Original-parent and exceptional-scalar labels represent a whole endpoint
fiber even if it is empty or has no incident interior branch. An explicit
homeomorphism transfers recursive slice covers to the exact fiber subtype
used by closed-slab gluing, with the same labels.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalSliceRepresentation
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (row parentCone)
open FlatAffineExceptionalSliceFrame (parent scalar slice)
open scoped Classical

noncomputable def fiberHomeomorph (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (hactive : h u ∈ FlatAffineFullSourceTower.free F u (F.depth u)) :
    ((FlatAffineShiftedSlice.projection F u (parent F C u v hv) (h u)) ⁻¹' {scalar F C h u a}) ≃ₜ
      slice F C h u v a hv :=
  (Topology.IsEmbedding.subtypeVal.homeomorphImage _).trans (Homeomorph.setCongr
    ((FlatAffineShiftedSlice.image_fiber F u (parent F C u v hv) (h u) hactive _).trans
      (FlatAffineExceptionalSliceFrame.slice_eq F C h u v a hv).symm))

noncomputable def endpointCover {I : Type*} (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (hactive : h u ∈ FlatAffineFullSourceTower.free F u (F.depth u))
    (cover : ClopenPathCover (slice F C h u v a hv) I) :
    ClopenPathCover ((FlatAffineShiftedSlice.projection F u (parent F C u v hv) (h u)) ⁻¹'
      {scalar F C h u a}) I :=
  cover.comap (fiberHomeomorph F C h u v a hv hactive)

theorem joined_iff (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (hactive : h u ∈ FlatAffineFullSourceTower.free F u (F.depth u))
    (y z : FlatAffineShiftedSlice.coarseSlice F u (parent F C u v hv) (h u))
    (hy : FlatAffineShiftedSlice.projection F u (parent F C u v hv) (h u) y = scalar F C h u a)
    (hz : FlatAffineShiftedSlice.projection F u (parent F C u v hv) (h u) z = scalar F C h u a) :
    JoinedIn ((FlatAffineShiftedSlice.projection F u (parent F C u v hv) (h u)) ⁻¹' {scalar F C h u a}) y z ↔
      JoinedIn (slice F C h u v a hv) y.val z.val := by
  rw [FlatAffineExceptionalSliceFrame.slice_eq]
  exact FlatAffineShiftedSlice.joined_fiber_iff F u (parent F C u v hv) (h u) hactive _ y z hy hz

/-- In particular this constructs a frame for isolated and empty fibers:
there is no hypothesis asserting a point or an incident branch. -/
theorem exists_endpoint_frame (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool)
    (hactive : h u ∈ FlatAffineFullSourceTower.free F u (F.depth u))
    (x : FlatAffinePowerSampleInput.OriginalRoots F u) (t : ℝ)
    (ht : SymbolicScaledSquarefree.scalarEvaluation t
      (FlatAffineHeightSlabExceptional.polynomial (next F) (row F h) u) = 0) :
    ∃ v a, ∃ hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v,
      FlatAffineExceptionalSliceFrame.record u v a ∈ FlatAffineExceptionalSliceFrame.language F C h ∧
        parent F C u v hv = x ∧ scalar F C h u a = t ∧
          Nonempty (((FlatAffineShiftedSlice.projection F u x (h u)) ⁻¹' {t}) ≃ₜ slice F C h u v a hv) := by
  obtain ⟨v, a, hv, H, hx, ht, _⟩ := FlatAffineExceptionalSliceFrame.exists_record F C h u x t ht
  refine ⟨v, a, hv, H, hx, ht, ?_⟩
  subst x
  subst t
  exact ⟨fiberHomeomorph F C h u v a hv hactive⟩

theorem exists_empty_slice_frame (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots F u) (t : ℝ)
    (ht : SymbolicScaledSquarefree.scalarEvaluation t
      (FlatAffineHeightSlabExceptional.polynomial (next F) (row F h) u) = 0)
    (hempty : FlatAffineShiftedSlice.slice F u x (h u) t = ∅) :
    ∃ v a, ∃ hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v,
      FlatAffineExceptionalSliceFrame.record u v a ∈ FlatAffineExceptionalSliceFrame.language F C h ∧
        slice F C h u v a hv = ∅ := by
  obtain ⟨v, a, hv, H, _, _, HS⟩ := FlatAffineExceptionalSliceFrame.exists_record F C h u x t ht
  exact ⟨v, a, hv, H, HS.trans hempty⟩

end LeanCanny.Connectivity.FlatAffineExceptionalSliceRepresentation

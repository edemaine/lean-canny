/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalEndpointFrame
public import LeanCanny.Connectivity.FlatAffineSlabCanonicalEndpoints
public import LeanCanny.Connectivity.ClopenPathCover

/-! # Actual slab endpoints inhabit exceptional frozen-parameter frames

The complete marker of each actual branch endpoint yields a frame whose
parent is the exact original frozen root and whose extra scalar is the
actual exceptional endpoint value. Its affine slice therefore denotes
exactly the endpoint fiber required by recursive slab gluing.

This proves representability, including singular endpoint fibers. Native
critical sampling and recursive covers for these new algebraic parameter
frames remain separate obligations.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalEndpointRepresentation
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineSlabGraphCodes (source endpointWord)
open FlatAffineSlabGraphArcs (original Index)
open FlatAffineSlabGraphContext (endpointValue)
open FlatAffineSlabGraphBranches (Family ParentIndex)
open FlatAffineLastHeightRow (row parentCone)
open scoped Classical
attribute [local irreducible] FlatAffineEndpointCanonicalParent.value SquareSampleCompleteVertices.candidate

variable {F : Inputs} {C : FlatAffinePowerPositive.ConeCertificate (next F)}
  {h : (u : List Bool) → Fin (arity F u)} {c : List Bool}

def marker (B : Family (next F) C (row F h) c) (side : Bool) (j : Index (next F) C (row F h) c) : List Bool :=
  pair (pair (source c) (endpointWord side c)) (B.reference side j)

noncomputable def query (B : Family (next F) C (row F h) c) (side : Bool)
    (j : Index (next F) C (row F h) c) : List Bool :=
  FlatAffineExceptionalEndpointFrame.frame F C h (marker B side j)

theorem query_valid (B : Family (next F) C (row F h) c) (side : Bool)
    (j : Index (next F) C (row F h) c) : query B side j ∈ FlatAffineExceptionalEndpointFrame.language F C h :=
  FlatAffineExceptionalEndpointFrame.frame_valid F C h _ (B.reference_marker_valid side j)

theorem query_original (B : Family (next F) C (row F h) c) (side : Bool)
    (j : Index (next F) C (row F h) c) : FlatAffineExceptionalEndpointFrame.original (query B side j) = original c := by
  simp only [query, FlatAffineExceptionalEndpointFrame.frame_original, marker, FlatAffineEndpointMarkers.source, pairFst_pair,
    FlatAffineJointPrefixChoice.original, FlatAffineSlabGraphArcs.original]

theorem query_scalar (B : Family (next F) C (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) C (row F h))
    (side : Bool) (j : Index (next F) C (row F h) c) :
    FlatAffineExceptionalEndpointFrame.scalar F C h (query B side j) (query_valid B side j) = endpointValue (next F) C (row F h) side c := by
  exact (FlatAffineExceptionalEndpointFrame.frame_scalar F C h (source c) (endpointWord side c)
    (B.reference side j) (B.reference_marker_valid side j)).trans
      (FlatAffineSlabGraphContext.endpointValue_packet (next F) C (row F h) side c hc).symm

theorem query_parentWord_valid (B : Family (next F) C (row F h) c) (side : Bool)
    (j : Index (next F) C (row F h) c) :
    FlatAffineCompleteVertices.Valid F (parentCone F C) (original c)
      (FlatAffineExceptionalEndpointFrame.parentWord (query B side j)) := by
  have HV := FlatAffineEndpointCanonicalParent.value_valid F C h (marker B side j)
    (B.reference_marker_valid side j)
  simpa only [query, FlatAffineExceptionalEndpointFrame.frame, FlatAffineExceptionalEndpointFrame.parentWord,
    marker, FlatAffineEndpointMarkers.source, FlatAffineJointPrefixChoice.original, pairFst_pair,
    pairSnd_pair, FlatAffineSlabGraphArcs.original] using HV

noncomputable def parentAt (B : Family (next F) C (row F h) c) (side : Bool)
    (j : Index (next F) C (row F h) c) : FlatAffinePowerSampleInput.OriginalRoots F (original c) :=
  FlatAffineCompleteVertices.vertexEquiv F (parentCone F C) (original c)
    ⟨FlatAffineExceptionalEndpointFrame.parentWord (query B side j), query_parentWord_valid B side j⟩

noncomputable def sliceAt (B : Family (next F) C (row F h) c) (side : Bool)
    (j : Index (next F) C (row F h) c) : Set (Fin (arity F (original c)) → ℝ) :=
  FlatAffineExceptionalEndpointFrame.presentation F h (original c) (parentAt B side j)
    (FlatAffineExceptionalEndpointFrame.scalar F C h (query B side j) (query_valid B side j))

section
variable [Fintype (Index (next F) C (row F h) c)] [LinearOrder (Index (next F) C (row F h) c)]

theorem query_parent (B : Family (next F) C (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) C (row F h))
    (hactive : h (original c) ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c))
    (side : Bool) (j : ParentIndex F C (row F h) c x) :
    parentAt B side j.val = x := by
  have H := B.reference_canonical_endpoint_filter hc side j.val
  have HE : FlatAffineEndpointCanonicalParent.value F C h (marker B side j.val) = B.canonicalParentWord side j.val := by
    simpa only [pairFst_pair, pairSnd_pair, marker] using H.2
  have HW : FlatAffineExceptionalEndpointFrame.parentWord (query B side j.val) = B.canonicalParentWord side j.val := by
    simpa only [FlatAffineExceptionalEndpointFrame.parentWord, query,
      FlatAffineExceptionalEndpointFrame.frame, pairSnd_pair] using HE
  have HV : (⟨FlatAffineExceptionalEndpointFrame.parentWord (query B side j.val), query_parentWord_valid B side j.val⟩ :
      {w : List Bool // FlatAffineCompleteVertices.Valid F (parentCone F C) (original c) w}) =
      ⟨B.canonicalParentWord side j.val, B.canonicalParentWord_valid hc side j.val⟩ := Subtype.ext HW
  exact (congrArg (FlatAffineCompleteVertices.vertexEquiv F (parentCone F C) (original c)) HV).trans
    (B.canonicalParentWord_exact hc hactive x side j)

theorem query_slice (B : Family (next F) C (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) C (row F h))
    (hactive : h (original c) ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c))
    (side : Bool) (j : ParentIndex F C (row F h) c x) :
    sliceAt B side j.val =
      FlatAffineShiftedSlice.slice F (original c) x (h (original c)) (endpointValue (next F) C (row F h) side c) := by
  exact (FlatAffineExceptionalEndpointFrame.presentation_eq_slice F h (original c) (parentAt B side j.val)
    (FlatAffineExceptionalEndpointFrame.scalar F C h (query B side j.val) (query_valid B side j.val))).trans
    (congrArg₂ (fun p a => FlatAffineShiftedSlice.slice F (original c) p (h (original c)) a)
      (query_parent B hc hactive x side j) (query_scalar B hc side j.val))

theorem query_fiber (B : Family (next F) C (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) C (row F h))
    (hactive : h (original c) ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c))
    (side : Bool) (j : ParentIndex F C (row F h) c x) :
    Subtype.val '' ((FlatAffineShiftedSlice.projection F (original c) x (h (original c))) ⁻¹'
      {endpointValue (next F) C (row F h) side c}) =
        sliceAt B side j.val :=
  (FlatAffineShiftedSlice.image_fiber F (original c) x (h (original c)) hactive _).trans
    (query_slice B hc hactive x side j).symm

/-- This is the actual subtype used by the endpoint-cover gluing API. -/
noncomputable def fiberHomeomorph (B : Family (next F) C (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) C (row F h))
    (hactive : h (original c) ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c))
    (side : Bool) (j : ParentIndex F C (row F h) c x) :
    ((FlatAffineShiftedSlice.projection F (original c) x (h (original c))) ⁻¹'
      {endpointValue (next F) C (row F h) side c}) ≃ₜ
        sliceAt B side j.val :=
  (Topology.IsEmbedding.subtypeVal.homeomorphImage _).trans
    (Homeomorph.setCongr (query_fiber B hc hactive x side j))

noncomputable def endpointCover {I : Type*} (B : Family (next F) C (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) C (row F h))
    (hactive : h (original c) ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c))
    (side : Bool) (j : ParentIndex F C (row F h) c x)
    (cover : ClopenPathCover
      (sliceAt B side j.val) I) :
    ClopenPathCover ((FlatAffineShiftedSlice.projection F (original c) x (h (original c))) ⁻¹'
      {endpointValue (next F) C (row F h) side c}) I :=
  cover.comap (fiberHomeomorph B hc hactive x side j)

end
end LeanCanny.Connectivity.FlatAffineExceptionalEndpointRepresentation

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabCanonicalParents
public import LeanCanny.Connectivity.FlatAffineSlabEndpointPrefixes
public import LeanCanny.Encoding.FlatAffineEndpointCanonicalParent

/-! # Actual endpoints retain the canonical original-context parent word

Re-encoding the endpoint copy's ancestor and the interior descriptor's ancestor
produces the same original-context word. Its decoded root is the exact frozen
parent, and the native endpoint filter accepts that same word at both limits.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineSlabGraphCodes (source endpointWord)
open FlatAffineSlabGraphArcs (original Index)
open FlatAffineLastHeightRow (row parentCone)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineBranchChoice.value FlatAffineBranchPrefixChoice.value
  FlatAffineBranchParentChoice.value SquareSampleContextRebase.value
  FlatAffineJointCopyPrefixChoice.value FlatAffineJointPrefixChoice.value

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate (next F)}
  {h : (u : List Bool) → Fin (arity F u)} {c : List Bool}
  [Fintype (Index (next F) cone (row F h) c)] [LinearOrder (Index (next F) cone (row F h) c)]

noncomputable def Family.canonicalEndpointWord (B : Family (next F) cone (row F h) c)
    (side : Bool) (j : Index (next F) cone (row F h) c) : List Bool :=
  SquareSampleContextRebase.value (FlatAffinePowerSampleInput.input F (parentCone F cone))
    FlatAffineJointPrefixChoice.original (pair (source c) (B.endpointPrefixWord side j))

theorem Family.canonicalEndpointWord_same (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (side : Bool) (j : Index (next F) cone (row F h) c) :
    B.canonicalEndpointWord side j = B.canonicalParentWord side j := by
  apply congrArg (fun w => SquareSampleContextRebase.value
    (FlatAffinePowerSampleInput.input F (parentCone F cone)) FlatAffineJointPrefixChoice.original (pair (source c) w))
  have HP : B.prefixWord side j = FlatAffineBranchParentChoice.value F cone h (B.sampleQuery side j) := by
    simpa only [FlatAffineBranchParentChoice.value] using B.prefixWord_program side j
  exact (B.endpointPrefixWord_same hc (FlatAffineLastHeightRow.ordinary F h _) side j).trans HP

theorem Family.canonicalEndpointWord_valid (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (side : Bool) (j : Index (next F) cone (row F h) c) :
    FlatAffineCompleteVertices.Valid F (parentCone F cone) (original c) (B.canonicalEndpointWord side j) := by
  rw [B.canonicalEndpointWord_same hc side j]
  exact B.canonicalParentWord_valid hc side j

theorem Family.canonicalEndpointWord_exact (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (hactive : h (original c) ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c))
    (side : Bool) (j : ParentIndex F cone (row F h) c x) :
    FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) (original c)
      ⟨B.canonicalEndpointWord side j.val, B.canonicalEndpointWord_valid hc side j.val⟩ = x := by
  have HE := B.canonicalEndpointWord_same hc side j.val
  have HV : (⟨B.canonicalEndpointWord side j.val, B.canonicalEndpointWord_valid hc side j.val⟩ :
      {w : List Bool // FlatAffineCompleteVertices.Valid F (parentCone F cone) (original c) w}) =
      ⟨B.canonicalParentWord side j.val, B.canonicalParentWord_valid hc side j.val⟩ := Subtype.ext HE
  exact (congrArg (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) (original c)) HV).trans
    (B.canonicalParentWord_exact hc hactive x side j)

theorem Family.reference_canonical_endpoint_filter (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (side : Bool) (j : Index (next F) cone (row F h) c) :
    pair (pair (pair (source c) (endpointWord side c)) (B.reference side j)) (B.canonicalParentWord side j) ∈
      FlatAffineEndpointCanonicalParent.language F cone h := by
  refine ⟨?_, ?_⟩
  · simpa only [pairFst_pair] using B.reference_marker_valid side j
  · simpa only [FlatAffineEndpointCanonicalParent.value, Function.comp_apply, FlatAffineEndpointCanonicalParent.parentRecord,
      FlatAffineEndpointAncestorMatch.value, FlatAffineEndpointMarkers.source, FlatAffineEndpointMarkers.jointQuery,
      FlatAffineEndpointMarkers.jointWord, Family.canonicalEndpointWord, Family.endpointPrefixWord,
      pairFst_pair, pairSnd_pair] using B.canonicalEndpointWord_same hc side j

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches

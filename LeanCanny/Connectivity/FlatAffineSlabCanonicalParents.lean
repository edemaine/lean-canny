/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabComputedParents
public import LeanCanny.Encoding.FlatAffineBranchCanonicalAncestorMatch

/-! # Original-context parent words select exact original slab components

The native descriptor filter accepts precisely the branches whose full
original ancestor tuple equals the decoded parent vertex. Re-encoded words
are valid in the original sampler used by recursive calls. The two retained
interior samples give the same canonical word, including singular parents.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineSlabGraphCodes (source)
open FlatAffineSlabGraphArcs (original Index)
open FlatAffineLastHeightRow (row parentCone)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineBranchChoice.value FlatAffineBranchPrefixChoice.value
  FlatAffineBranchParentChoice.value SquareSampleContextRebase.value
  FlatAffineEndpointBranchLabels.language

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate (next F)}
  {h : (u : List Bool) → Fin (arity F u)} {c : List Bool}
  [Fintype (Index (next F) cone (row F h) c)] [LinearOrder (Index (next F) cone (row F h) c)]

noncomputable def Family.canonicalParentWord (B : Family (next F) cone (row F h) c)
    (side : Bool) (j : Index (next F) cone (row F h) c) : List Bool :=
  SquareSampleContextRebase.value (FlatAffinePowerSampleInput.input F (parentCone F cone))
    FlatAffineJointPrefixChoice.original
    (pair (source c) (FlatAffineBranchParentChoice.value F cone h (B.sampleQuery side j)))

omit [Fintype (Index (next F) cone (row F h) c)] [LinearOrder (Index (next F) cone (row F h) c)] in
theorem Family.canonicalParentWord_eq_value (B : Family (next F) cone (row F h) c)
    (side : Bool) (j : Index (next F) cone (row F h) c) :
    B.canonicalParentWord side j = FlatAffineBranchCanonicalParent.value F cone h (B.sampleQuery side j) := by
  exact congrArg (fun s => SquareSampleContextRebase.value
    (FlatAffinePowerSampleInput.input F (parentCone F cone)) FlatAffineJointPrefixChoice.original
      (pair s (FlatAffineBranchParentChoice.value F cone h (B.sampleQuery side j))))
    (B.parent_query_source side j).symm

theorem Family.canonicalParentWord_valid (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (side : Bool) (j : Index (next F) cone (row F h) c) :
    FlatAffineCompleteVertices.Valid F (parentCone F cone) (original c) (B.canonicalParentWord side j) :=
  SquareSampleContextRebase.value_valid _ (FlatAffinePowerSampleInput.complete F (parentCone F cone))
    FlatAffineJointPrefixChoice.original (source c) _
    (FlatAffineBranchParentChoice.value_valid_at F cone h (B.sampleQuery side j) (source c)
      (B.parent_query_valid hc side j) (B.parent_query_source side j))

theorem Family.canonicalParentWord_parent (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (side : Bool) (j : Index (next F) cone (row F h) c) :
    FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) (original c)
      ⟨B.canonicalParentWord side j, B.canonicalParentWord_valid hc side j⟩ = B.computedParent hc side j := by
  have HP := SquareSampleContextRebase.value_point _ (FlatAffinePowerSampleInput.complete F (parentCone F cone))
    FlatAffineJointPrefixChoice.original (source c) _
    (FlatAffineBranchParentChoice.value_valid_at F cone h (B.sampleQuery side j) (source c)
      (B.parent_query_valid hc side j) (B.parent_query_source side j))
  apply congrArg (FlatAffinePowerSampleInput.originalRootsEquiv F (original c))
  exact Subtype.ext HP

theorem Family.canonicalParentWord_anchor (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (hactive : h (original c) ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (side : Bool) (j : Index (next F) cone (row F h) c) :
    (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) (original c)
      ⟨B.canonicalParentWord side j, B.canonicalParentWord_valid hc side j⟩).val =
      FlatAffineShiftedSlice.ancestorPoint F (original c) j.val :=
  (congrArg Subtype.val (B.canonicalParentWord_parent hc side j)).trans (B.computedParent_anchor hc hactive side j)

theorem Family.canonicalParentWord_exact (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (hactive : h (original c) ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c))
    (side : Bool) (j : ParentIndex F cone (row F h) c x) :
    FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) (original c)
      ⟨B.canonicalParentWord side j.val, B.canonicalParentWord_valid hc side j.val⟩ = x :=
  (B.canonicalParentWord_parent hc side j.val).trans (B.computedParent_exact hc hactive x side j)

theorem Family.canonicalParentWord_same (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (hactive : h (original c) ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (j : Index (next F) cone (row F h) c) : B.canonicalParentWord false j = B.canonicalParentWord true j := by
  have HE := Subtype.ext ((B.canonicalParentWord_anchor hc hactive false j).trans
    (B.canonicalParentWord_anchor hc hactive true j).symm)
  exact congrArg Subtype.val ((FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) (original c)).injective HE)

theorem Family.canonical_filter_index_packet (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (hactive : h (original c) ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (side : Bool) (j : Index (next F) cone (row F h) c) (v : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) (original c) v) :
    pair (B.sampleQuery side j) v ∈ FlatAffineBranchCanonicalAncestorMatch.language F cone h ↔
      FlatAffineShiftedSlice.ancestorPoint F (original c) j.val =
        (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) (original c) ⟨v, hv⟩).val := by
  have HQ := B.parent_query_valid hc side j
  have HP := B.canonicalParentWord_anchor hc hactive side j
  simp only [FlatAffineBranchCanonicalAncestorMatch.language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, HQ, true_and]
  rw [← B.canonicalParentWord_eq_value side j]
  constructor
  · intro he
    subst v
    exact HP.symm
  · intro he
    have HE := Subtype.ext (HP.trans he)
    exact congrArg Subtype.val ((FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) (original c)).injective HE)

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches

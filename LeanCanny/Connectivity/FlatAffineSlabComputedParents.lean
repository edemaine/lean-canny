/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabParentBranches
public import LeanCanny.Connectivity.FlatAffineSlabBranchParents
public import LeanCanny.Encoding.FlatAffineBranchOriginalAncestorMatch

/-! # Native computed parents agree with the original slab component family -/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineSlabGraphCodes (source)
open FlatAffineSlabGraphArcs (original Index)
open FlatAffineSlabGraphContext (sampleValue)
open FlatAffineLastHeightRow (row parentCone)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineBranchChoice.value FlatAffineBranchPrefixChoice.value
  FlatAffineEndpointBranchLabels.language

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate (next F)}
  {h : (u : List Bool) → Fin (arity F u)} {c : List Bool}
  [Fintype (Index (next F) cone (row F h) c)] [LinearOrder (Index (next F) cone (row F h) c)]

omit [Fintype (Index (next F) cone (row F h) c)] [LinearOrder (Index (next F) cone (row F h) c)] in
theorem Family.parent_query_source (B : Family (next F) cone (row F h) c)
    (side : Bool) (j : Index (next F) cone (row F h) c) :
    FlatAffineEndpointBranchLabels.source (B.sampleQuery side j) = source c := by
  simp only [Family.sampleQuery, FlatAffineEndpointBranchLabels.source, pairFst_pair]

theorem Family.parent_query_valid (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (side : Bool) (j : Index (next F) cone (row F h) c) :
    B.sampleQuery side j ∈ FlatAffineEndpointBranchLabels.language (next F) cone (row F h) :=
  (B.labels_iff hc side _).mpr ⟨j, rfl⟩

noncomputable def Family.computedParent (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (side : Bool) (j : Index (next F) cone (row F h) c) : FlatAffinePowerSampleInput.OriginalRoots F (original c) :=
  FlatAffineBranchParentChoice.decode F (parentCone F cone) (source c)
    (FlatAffineBranchParentChoice.value F cone h (B.sampleQuery side j))
    (FlatAffineBranchParentChoice.value_valid_at F cone h (B.sampleQuery side j) (source c)
      (B.parent_query_valid hc side j) (B.parent_query_source side j))

theorem Family.computedParent_point (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (side : Bool) (j : Index (next F) cone (row F h) c) :
    (B.computedParent hc side j).val =
      FlatAffineShiftedSlice.ancestorPoint F (original c) (B.curve j (sampleValue (next F) cone (row F h) side c)) := by
  have HP := FlatAffineBranchParentChoice.parent_val_at F cone h (B.sampleQuery side j) (source c)
    (B.parent_query_valid hc side j) (B.parent_query_source side j)
  have HC : FlatAffineBranchParentChoice.currentAt F cone h (source c) (B.sampleQuery side j) =
      B.curve j (sampleValue (next F) cone (row F h) side c) := B.selected_current hc side j
  exact HP.trans (congrArg (FlatAffineShiftedSlice.ancestorPoint F (original c)) HC)

theorem Family.computedParent_exact (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (hactive : h (original c) ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c))
    (side : Bool) (j : ParentIndex F cone (row F h) c x) : B.computedParent hc side j.val = x := by
  have HT := Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between (next F) cone (row F h) side c hc)
  exact Subtype.ext ((B.computedParent_point hc side j.val).trans
    (B.parent_ancestor F cone (row F h) c hc (h (original c)) rfl hactive x j ⟨_, HT⟩))

theorem Family.original_filter_packet (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (side : Bool) (j : Index (next F) cone (row F h) c) (v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid
      (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F (parentCone F cone)) FlatAffineJointPrefixChoice.original) (source c) v) :
    pair (B.sampleQuery side j) v ∈ FlatAffineBranchOriginalAncestorMatch.language F cone h ↔
      B.computedParent hc side j = FlatAffineBranchParentChoice.decode F (parentCone F cone) (source c) v hv := by
  have HQ := B.parent_query_valid hc side j
  have HW := FlatAffineBranchParentChoice.value_valid_at F cone h (B.sampleQuery side j) (source c) HQ (B.parent_query_source side j)
  simp only [FlatAffineBranchOriginalAncestorMatch.language, FlatAffineBranchAncestorMatch.language,
    Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, HQ, true_and]
  change FlatAffineBranchParentChoice.value F cone h (B.sampleQuery side j) = v ↔ _
  constructor
  · intro he
    subst v
    rfl
  · intro he
    exact FlatAffineBranchParentChoice.decode_injective F (parentCone F cone) (source c) _ v HW hv he

theorem Family.computedParent_anchor (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (hactive : h (original c) ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (side : Bool) (j : Index (next F) cone (row F h) c) :
    (B.computedParent hc side j).val = FlatAffineShiftedSlice.ancestorPoint F (original c) j.val := by
  have HS := Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between (next F) cone (row F h) side c hc)
  have HT := Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between (next F) cone (row F h) false c hc)
  have HE := B.original_ancestor_constant F cone (row F h) c (h (original c)) rfl hactive j ⟨_, HS⟩ ⟨_, HT⟩
  exact (B.computedParent_point hc side j).trans
    (HE.trans (congrArg (FlatAffineShiftedSlice.ancestorPoint F (original c)) (B.anchor j)))

theorem Family.original_filter_index_packet (B : Family (next F) cone (row F h) c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone (row F h))
    (hactive : h (original c) ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (side : Bool) (j : Index (next F) cone (row F h) c) (v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid
      (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F (parentCone F cone)) FlatAffineJointPrefixChoice.original) (source c) v) :
    pair (B.sampleQuery side j) v ∈ FlatAffineBranchOriginalAncestorMatch.language F cone h ↔
      FlatAffineShiftedSlice.ancestorPoint F (original c) j.val =
        (FlatAffineBranchParentChoice.decode F (parentCone F cone) (source c) v hv).val := by
  have HP := B.computedParent_anchor hc hactive side j
  constructor
  · intro he
    exact HP.symm.trans (congrArg Subtype.val ((B.original_filter_packet hc side j v hv).mp he))
  · intro he
    exact (B.original_filter_packet hc side j v hv).mpr (Subtype.ext (HP.trans he))

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches

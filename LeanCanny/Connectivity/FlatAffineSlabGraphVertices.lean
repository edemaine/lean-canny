/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabGraphAttachments
public import LeanCanny.Encoding.FlatAffineEndpointMarkerComplete

/-! # Every native slab vertex denotes one actual geometric piece

Branch descriptors denote unique constructed curves. Endpoint markers denote
their recovered points, independently of auxiliary copies and padding. Every
geometric piece has a valid word of the graph's derived width.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes
open FlatAffineSlabGraphArcs (original equation)
open FlatAffineSlabGraphContext (endpointValue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

abbrev PieceIndex (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool) :=
  FiniteFiberSlab.Index (equation F height c) (FlatAffineSlabGraphArcs.Index F cone height c)
    (endpointValue F cone height false c) (endpointValue F cone height true c)

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate F}
  {height : (u : List Bool) → Fin (count F u)} {c : List Bool}
  [Fintype (FlatAffineSlabGraphArcs.Index F cone height c)] [LinearOrder (FlatAffineSlabGraphArcs.Index F cone height c)]

noncomputable def Family.Denotes (B : Family F cone height c) (w : List Bool) : PieceIndex F cone height c → Prop
  | .inl j => kind w = 0 ∧ branchPayload F cone height (pair c w) = B.descriptor false j
  | .inr (.inl x) => kind w = 1 ∧
    pair (pair (source c) (endpointWord false c)) (markerPayload F cone height (pair c w)) ∈ FlatAffineEndpointMarkers.language F cone height ∧
    markerPoint F cone height c (markerPayload F cone height (pair c w)) = x.val
  | .inr (.inr x) => kind w = 2 ∧
    pair (pair (source c) (endpointWord true c)) (markerPayload F cone height (pair c w)) ∈ FlatAffineEndpointMarkers.language F cone height ∧
    markerPoint F cone height c (markerPayload F cone height (pair c w)) = x.val

theorem Family.valid_iff_denotes (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (w : List Bool) :
    pair c w ∈ FlatAffineSlabGraph.validLanguage F cone height ↔ ∃ i, B.Denotes w i := by
  simp only [FlatAffineSlabGraph.validLanguage, Set.mem_union, FlatAffineSlabGraph.guardLanguage,
    Set.mem_ofPred_eq, Set.mem_preimage, pairSnd_pair]
  constructor
  · rintro (⟨hk, hb⟩ | ⟨hk, hm⟩ | ⟨hk, hm⟩)
    · have HB : pair (pair (source c) (pair (sampleWord false c) (gapWord c))) (branchPayload F cone height (pair c w)) ∈
          FlatAffineEndpointBranchLabels.language F cone height := by
        simpa only [branchQuery, pairFst_pair] using hb
      obtain ⟨j, hj⟩ := (B.labels_iff hc false _).mp HB
      exact ⟨.inl j, hk, hj.symm⟩
    · have HM : pair (pair (source c) (endpointWord false c)) (markerPayload F cone height (pair c w)) ∈
          FlatAffineEndpointMarkers.language F cone height := by
        simpa only [markerQuery, pairFst_pair] using hm
      exact ⟨.inr (.inl ⟨_, markerPoint_in_fiber hc false _ HM⟩), hk, HM, rfl⟩
    · have HM : pair (pair (source c) (endpointWord true c)) (markerPayload F cone height (pair c w)) ∈
          FlatAffineEndpointMarkers.language F cone height := by
        simpa only [markerQuery, pairFst_pair] using hm
      exact ⟨.inr (.inr ⟨_, markerPoint_in_fiber hc true _ HM⟩), hk, HM, rfl⟩
  · rintro ⟨j | (x | x), hj⟩
    · refine Or.inl ⟨hj.1, ?_⟩
      have HB := (B.labels_iff hc false _).mpr ⟨j, hj.2.symm⟩
      simpa only [branchQuery, pairFst_pair] using HB
    · exact Or.inr (Or.inl ⟨hj.1, by simpa only [markerQuery, pairFst_pair] using hj.2.1⟩)
    · exact Or.inr (Or.inr ⟨hj.1, by simpa only [markerQuery, pairFst_pair] using hj.2.1⟩)

theorem Family.denotes_unique (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (w : List Bool)
    {i j : PieceIndex F cone height c} (hi : B.Denotes w i) (hj : B.Denotes w j) : i = j := by
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  · exact congrArg Sum.inl (B.descriptors_injective hc false (hi.2.symm.trans hj.2))
  · have H := hi.1.symm.trans hj.1; norm_num at H
  · have H := hi.1.symm.trans hj.1; norm_num at H
  · have H := hi.1.symm.trans hj.1; norm_num at H
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (Subtype.ext (hi.2.2.symm.trans hj.2.2))
  · have H := hi.1.symm.trans hj.1; norm_num at H
  · have H := hi.1.symm.trans hj.1; norm_num at H
  · have H := hi.1.symm.trans hj.1; norm_num at H
  · exact congrArg (fun x => Sum.inr (Sum.inr x)) (Subtype.ext (hi.2.2.symm.trans hj.2.2))

theorem Family.denotes_surjective (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (i : PieceIndex F cone height c) :
    ∃ w, w.length = width F cone height c ∧ B.Denotes w i := by
  rcases i with j | (x | x)
  · let d := B.descriptor false j
    have HB := (B.labels_iff hc false d).mpr ⟨j, rfl⟩
    have HD : d.length = descriptorWidth F cone height c := by
      simpa only [FlatAffineEndpointBranchLabels.descriptor, FlatAffineEndpointBranchLabels.source,
        pairFst_pair, pairSnd_pair, descriptorWidth, jointWidth] using FlatAffineEndpointBranchLabels.valid_length F cone height _ HB
    exact ⟨branchNode F cone height c d, (FlatAffineSlabGraph.branchNode_valid F cone height c d HB).1,
      branchNode_kind F cone height c d, branchNode_payload F cone height c d HD⟩
  · obtain ⟨w, hm, he⟩ := markerPoint_complete hc false x.val x.property
    have HW : w.length = jointWidth F cone height c := by
      simpa only [FlatAffineEndpointMarkers.jointWord, FlatAffineEndpointMarkers.source,
        pairFst_pair, pairSnd_pair, jointWidth] using FlatAffineEndpointMarkers.valid_length F cone height _ hm
    refine ⟨markerNode F cone height false c w, (FlatAffineSlabGraph.markerNode_valid F cone height false c w hm).1, ?_⟩
    change kind _ = 1 ∧ _
    rw [markerNode_payload F cone height false c w HW]
    exact ⟨by simpa only [Bool.false_eq_true, ite_false] using markerNode_kind F cone height false c w, hm, he⟩
  · obtain ⟨w, hm, he⟩ := markerPoint_complete hc true x.val x.property
    have HW : w.length = jointWidth F cone height c := by
      simpa only [FlatAffineEndpointMarkers.jointWord, FlatAffineEndpointMarkers.source,
        pairFst_pair, pairSnd_pair, jointWidth] using FlatAffineEndpointMarkers.valid_length F cone height _ hm
    refine ⟨markerNode F cone height true c w, (FlatAffineSlabGraph.markerNode_valid F cone height true c w hm).1, ?_⟩
    change kind _ = 2 ∧ _
    rw [markerNode_payload F cone height true c w HW]
    exact ⟨by simpa only [ite_true] using markerNode_kind F cone height true c w, hm, he⟩

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches

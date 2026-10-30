/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSlabGraphCodes
public import LeanCanny.Computation.PSPACEBoolean

/-! # Native validity and adjacency of the concrete slab graph

Branch vertices carry validated short descriptors. Endpoint vertices carry
validated complete point markers. Equality handles duplicate marker names;
the checked attachment query supplies both orientations of each arc edge.
All routines include their own native readers and bounded searches.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSlabGraph
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def guardLanguage (P : List Bool → Prop) (L : Language) : Language := {q | P q ∧ q ∈ L}
private theorem guardDecider {P : List Bool → Prop} (hP : FPPred P) {L : Language} (D : SpaceDecider L) :
    SpaceDecider (guardLanguage P L) := by
  apply ((SpaceFunction.ofFP _ hP.flag_mem_FP).andFlags D.flagEvaluator).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [guardLanguage, Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq]
private theorem fpDecider {P : List Bool → Prop} (hP : FPPred P) : SpaceDecider {q | P q} := by
  apply (SpaceFunction.ofFP _ hP.flag_mem_FP).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq]

noncomputable def validLanguage (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  guardLanguage (fun q => kind (pairSnd q) = 0)
      (branchQuery F cone height ⁻¹' FlatAffineEndpointBranchLabels.language F cone height) ∪
    (guardLanguage (fun q => kind (pairSnd q) = 1)
      (markerQuery F cone height false ⁻¹' FlatAffineEndpointMarkers.language F cone height) ∪
    guardLanguage (fun q => kind (pairSnd q) = 2)
      (markerQuery F cone height true ⁻¹' FlatAffineEndpointMarkers.language F cone height))

theorem validDecider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceDecider (validLanguage F cone height) := by
  have K : BinaryFn (fun q => kind (pairSnd q)) := kind_binary.comp pairSnd_mem_FP
  have B := (FlatAffineEndpointBranchLabels.decider h cone height hh).precompose (branchQuery F cone height) (branchQuery_FP h cone height hh)
  have L := (FlatAffineEndpointMarkers.decider h cone height hh).precompose (markerQuery F cone height false) (markerQuery_FP h cone height hh false)
  have R := (FlatAffineEndpointMarkers.decider h cone height hh).precompose (markerQuery F cone height true) (markerQuery_FP h cone height hh true)
  exact (guardDecider (K.eq (BinaryFn.const 0)) B).union
    ((guardDecider (K.eq (BinaryFn.const 1)) L).union (guardDecider (K.eq (BinaryFn.const 2)) R))

def tagPair (i j : ℕ) (r : List Bool) : Prop := kind (pairFst (pairSnd r)) = i ∧ kind (pairSnd (pairSnd r)) = j
theorem tagPair_pred (i j : ℕ) : FPPred (tagPair i j) := by
  have L : BinaryFn (fun r => kind (pairFst (pairSnd r))) := kind_binary.comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have R : BinaryFn (fun r => kind (pairSnd (pairSnd r))) := kind_binary.comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  exact (L.eq (BinaryFn.const i)).and (R.eq (BinaryFn.const j))

noncomputable def branchEquality (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {r | branchPayload F cone height (leftVertex r) = branchPayload F cone height (rightVertex r)}
theorem branchEqualityDecider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider (branchEquality F cone height) :=
  fpDecider (Brackets.stringEq_fppred (mem_FP_comp leftVertex_FP (branchPayload_FP h cone height hh))
    (mem_FP_comp rightVertex_FP (branchPayload_FP h cone height hh)))

noncomputable def rawEdgeLanguage (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  guardLanguage (tagPair 0 0) (branchEquality F cone height) ∪
  (guardLanguage (tagPair 1 1) (markerEqualityQuery F cone height false ⁻¹' FlatAffineEndpointMarkerEquality.language F cone height) ∪
  (guardLanguage (tagPair 2 2) (markerEqualityQuery F cone height true ⁻¹' FlatAffineEndpointMarkerEquality.language F cone height) ∪
  (guardLanguage (tagPair 0 1) (attachmentQuery F cone height false ⁻¹' FlatAffineEndpointIncidenceQuery.language F cone height true) ∪
  (guardLanguage (tagPair 0 2) (attachmentQuery F cone height true ⁻¹' FlatAffineEndpointIncidenceQuery.language F cone height false) ∪
  (guardLanguage (tagPair 1 0) ((attachmentQuery F cone height false ∘ swap) ⁻¹' FlatAffineEndpointIncidenceQuery.language F cone height true) ∪
   guardLanguage (tagPair 2 0) ((attachmentQuery F cone height true ∘ swap) ⁻¹' FlatAffineEndpointIncidenceQuery.language F cone height false))))))

theorem rawEdgeDecider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceDecider (rawEdgeLanguage F cone height) := by
  have B := branchEqualityDecider h cone height hh
  have M := FlatAffineEndpointMarkerEquality.decider h cone height hh
  have L := FlatAffineEndpointIncidenceQuery.decider h cone height hh true
  have R := FlatAffineEndpointIncidenceQuery.decider h cone height hh false
  have LL := M.precompose (markerEqualityQuery F cone height false) (markerEqualityQuery_FP h cone height hh false)
  have RR := M.precompose (markerEqualityQuery F cone height true) (markerEqualityQuery_FP h cone height hh true)
  have BL := L.precompose (attachmentQuery F cone height false) (attachmentQuery_FP h cone height hh false)
  have BR := R.precompose (attachmentQuery F cone height true) (attachmentQuery_FP h cone height hh true)
  have LB := L.precompose (attachmentQuery F cone height false ∘ swap) (mem_FP_comp swap_FP (attachmentQuery_FP h cone height hh false))
  have RB := R.precompose (attachmentQuery F cone height true ∘ swap) (mem_FP_comp swap_FP (attachmentQuery_FP h cone height hh true))
  exact (guardDecider (tagPair_pred 0 0) B).union
    ((guardDecider (tagPair_pred 1 1) LL).union ((guardDecider (tagPair_pred 2 2) RR).union
    ((guardDecider (tagPair_pred 0 1) BL).union ((guardDecider (tagPair_pred 0 2) BR).union
    ((guardDecider (tagPair_pred 1 0) LB).union (guardDecider (tagPair_pred 2 0) RB))))))

noncomputable def edgeLanguage (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {r | leftVertex r ∈ validLanguage F cone height ∧ rightVertex r ∈ validLanguage F cone height ∧ r ∈ rawEdgeLanguage F cone height}
theorem edgeDecider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider (edgeLanguage F cone height) := by
  have D := validDecider h cone height hh
  have L := (D.precompose leftVertex leftVertex_FP).flagEvaluator
  have R := (D.precompose rightVertex rightVertex_FP).flagEvaluator
  have E := (rawEdgeDecider h cone height hh).flagEvaluator
  apply (L.andFlags (R.andFlags E)).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro r
  simp only [edgeLanguage, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem valid_mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : validLanguage F cone height ∈ PSPACE :=
  (validDecider h cone height hh).mem_PSPACE
theorem edge_mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : edgeLanguage F cone height ∈ PSPACE :=
  (edgeDecider h cone height hh).mem_PSPACE

theorem branchNode_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c d : List Bool)
    (hB : pair (pair (source c) (pair (sampleWord false c) (gapWord c))) d ∈ FlatAffineEndpointBranchLabels.language F cone height) :
    (branchNode F cone height c d).length = width F cone height c ∧
      pair c (branchNode F cone height c d) ∈ validLanguage F cone height := by
  have HD : d.length = descriptorWidth F cone height c := by
    simpa only [FlatAffineEndpointBranchLabels.descriptor, FlatAffineEndpointBranchLabels.source,
      pairFst_pair, pairSnd_pair, descriptorWidth, jointWidth] using FlatAffineEndpointBranchLabels.valid_length F cone height _ hB
  refine ⟨branchNode_length F cone height c d HD, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · simpa only [pairSnd_pair] using branchNode_kind F cone height c d
  · change branchQuery F cone height (pair c (branchNode F cone height c d)) ∈ FlatAffineEndpointBranchLabels.language F cone height
    simpa only [branchQuery, pairFst_pair, branchNode_payload F cone height c d HD] using hB

theorem markerNode_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (c w : List Bool)
    (hM : pair (pair (source c) (endpointWord right c)) w ∈ FlatAffineEndpointMarkers.language F cone height) :
    (markerNode F cone height right c w).length = width F cone height c ∧
      pair c (markerNode F cone height right c w) ∈ validLanguage F cone height := by
  have HW : w.length = jointWidth F cone height c := by
    simpa only [FlatAffineEndpointMarkers.jointWord, FlatAffineEndpointMarkers.source,
      pairFst_pair, pairSnd_pair, jointWidth] using FlatAffineEndpointMarkers.valid_length F cone height _ hM
  have HQ : markerQuery F cone height right (pair c (markerNode F cone height right c w)) ∈ FlatAffineEndpointMarkers.language F cone height := by
    simpa only [markerQuery, pairFst_pair, markerNode_payload F cone height right c w HW] using hM
  refine ⟨markerNode_length F cone height right c w HW, ?_⟩
  cases right
  · exact Or.inr (Or.inl ⟨by simpa only [pairSnd_pair, Bool.false_eq_true, ite_false] using markerNode_kind F cone height false c w, HQ⟩)
  · exact Or.inr (Or.inr ⟨by simpa only [pairSnd_pair, ite_true] using markerNode_kind F cone height true c w, HQ⟩)

end LeanCanny.Encoding.FlatAffineSlabGraph

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineBranchCanonicalParent

/-! # Native exact-ancestor filtering of short branch descriptors

The query pairs a native branch descriptor with an original-context ancestor
word. The program validates the descriptor, computes its ancestor word, and
compares the two words. No ancestor comparison oracle is supplied.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineBranchCanonicalAncestorMatch
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineJointPrefixChoice (original)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointBranchLabels (source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineBranchCanonicalParent.value FlatAffineBranchChoice.value
  FlatAffineEndpointBranchLabels.language FlatAffineJointPrefixChoice.value

noncomputable def language (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) : Language :=
  {q | pairFst q ∈ FlatAffineEndpointBranchLabels.language (next F) C (FlatAffineLastHeightRow.row F h) ∧
    FlatAffineBranchCanonicalParent.value F C h (pairFst q) = pairSnd q}

theorem decider {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    SpaceDecider (language F C h) := by
  have V := ((FlatAffineBranchCanonicalParent.evaluator hF C h hh).precompose pairFst pairFst_mem_FP).pairOutputs
    (SpaceFunction.ofFP pairSnd pairSnd_mem_FP)
  have E := V.postcompose (fun q => [decide (pairFst q = pairSnd q)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have D := ((FlatAffineEndpointBranchLabels.decider (FlatAffineCompleteRootStages.access hF (hF.depth.add (UnaryFn.const 1))) C
    (FlatAffineLastHeightRow.row F h) (FlatAffineLastHeightRow.row_unary hF h hh)).precompose pairFst pairFst_mem_FP).flagEvaluator
  apply (D.andFlags E).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]
  rfl

theorem mem_PSPACE {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    language F C h ∈ PSPACE := (decider hF C h hh).mem_PSPACE

theorem packet (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q v : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language (next F) C (FlatAffineLastHeightRow.row F h))
    (hv : FlatAffineCompleteVertices.Valid F (FlatAffineLastHeightRow.parentCone F C) (original (source q)) v) :
    pair q v ∈ language F C h ↔ FlatAffineBranchParentChoice.parent F C h q hq =
      FlatAffineCompleteVertices.vertexEquiv F (FlatAffineLastHeightRow.parentCone F C) (original (source q)) ⟨v, hv⟩ := by
  simp only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, hq, true_and]
  constructor
  · intro he
    subst v
    exact (FlatAffineBranchCanonicalParent.value_parent F C h q hq).symm
  · intro he
    have H := (FlatAffineCompleteVertices.vertexEquiv F (FlatAffineLastHeightRow.parentCone F C)
      (original (source q))).injective ((FlatAffineBranchCanonicalParent.value_parent F C h q hq).trans he)
    exact congrArg Subtype.val H

theorem tuple_packet (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q v : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language (next F) C (FlatAffineLastHeightRow.row F h))
    (hv : FlatAffineCompleteVertices.Valid F (FlatAffineLastHeightRow.parentCone F C) (original (source q)) v) :
    pair q v ∈ language F C h ↔
      FlatAffineShiftedSlice.ancestorPoint F (original (source q)) (FlatAffineBranchParentChoice.current F C h q) =
        (FlatAffineCompleteVertices.vertexEquiv F (FlatAffineLastHeightRow.parentCone F C) (original (source q)) ⟨v, hv⟩).val := by
  constructor
  · intro he
    exact (FlatAffineBranchParentChoice.parent_val F C h q hq).symm.trans
      (congrArg Subtype.val ((packet F C h q v hq hv).mp he))
  · intro he
    exact (packet F C h q v hq hv).mpr
      (Subtype.ext ((FlatAffineBranchParentChoice.parent_val F C h q hq).trans he))

end LeanCanny.Encoding.FlatAffineBranchCanonicalAncestorMatch

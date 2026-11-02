/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryCandidateNonempty

/-! # Native packets for bounded Boolean sign/component labels

The original sign word precedes the actual closed-source candidate. Extra
candidate-budget bits must be zero. Every semantic tag has a native writer
and exact source/candidate readback. Original-equation decision cost is
supplied by the separate joint-bank term filter.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryCandidateLabels
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def signWidth (original : List Bool) := 2*ClosedFormulaGateMetadata.count original
noncomputable def sign (q : List Bool) := (pairSnd q).take (signWidth (pairFst q))
noncomputable def source (q : List Bool) := pair (pairFst q) (sign q)
noncomputable def candidate (q : List Bool) :=
  ((pairSnd q).drop (signWidth (pairFst q))).take (CanonicalAuxiliaryCandidateCover.width (source q))
noncomputable def padding (q : List Bool) :=
  ((pairSnd q).drop (signWidth (pairFst q))).drop (CanonicalAuxiliaryCandidateCover.width (source q))

theorem signWidth_unary : UnaryFn signWidth := (UnaryFn.const 2).mul ClosedFormulaGateMetadata.count_unary
theorem sign_FP : sign∈FP := take_mem_FP pairSnd_mem_FP (signWidth_unary.comp pairFst_mem_FP)
theorem source_FP : source∈FP := mem_FP_pair pairFst_mem_FP sign_FP
theorem candidate_FP : candidate∈FP :=
  take_mem_FP (drop_mem_FP pairSnd_mem_FP (signWidth_unary.comp pairFst_mem_FP))
    (CanonicalAuxiliaryCandidateCover.width_unary.comp source_FP)
theorem padding_FP : padding∈FP :=
  drop_mem_FP (drop_mem_FP pairSnd_mem_FP (signWidth_unary.comp pairFst_mem_FP))
    (CanonicalAuxiliaryCandidateCover.width_unary.comp source_FP)

def Guard (q : List Bool) : Prop :=
  (pairSnd q).length=CanonicalAuxiliaryCandidateCover.tagWidth (pairFst q) ∧ (padding q).count true=0

theorem guard_FP : FPPred Guard :=
  (FPPred.eq (UnaryFn.length pairSnd_mem_FP) (CanonicalAuxiliaryCandidateCover.tagWidth_unary.comp pairFst_mem_FP)).and
    (FPPred.eq (Brackets.countTrue_unary.comp padding_FP) (UnaryFn.const 0))

noncomputable def writer (p : List Bool) : List Bool := pair (pairFst p)
  (IntegralMixedAuxiliaryCandidate.pad (signWidth (pairFst p)) (pairFst (pairSnd p))++
    IntegralMixedAuxiliaryCandidate.pad (CanonicalAuxiliaryCandidateCover.labelBudget (pairFst p)) (pairSnd (pairSnd p)))

theorem writer_FP : writer∈FP :=
  mem_FP_pair pairFst_mem_FP (appendFn_mem_FP
    (IntegralMixedAuxiliaryCandidate.pad_FP (signWidth_unary.comp pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))
    (IntegralMixedAuxiliaryCandidate.pad_FP (CanonicalAuxiliaryCandidateCover.labelBudget_unary.comp pairFst_mem_FP)
      (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)))

theorem writer_encode (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d) :
    writer (pair (CanonicalSignRefinement.original d) (pair i.1.val i.2.val))=
      pair (CanonicalSignRefinement.original d) (CanonicalAuxiliaryCandidateCover.encode d i) := by
  have HL : i.2.val.length≤CanonicalAuxiliaryCandidateCover.labelBudget (CanonicalSignRefinement.original d) :=
    i.2.property.le.trans (CanonicalAuxiliaryCandidateCover.label_le_budget d i.1)
  unfold writer
  simp only [pairFst_pair,pairSnd_pair]
  rw [IntegralMixedAuxiliaryCandidate.pad_eq _ _ HL]
  have HS : signWidth (CanonicalSignRefinement.original d)=i.1.val.length := i.1.property.1.symm
  rw [HS,IntegralMixedAuxiliaryCandidate.pad_eq _ _ (Nat.le_refl _),Nat.sub_self,List.replicate_zero,List.append_nil]
  rfl

theorem sign_encode (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d) :
    sign (pair (CanonicalSignRefinement.original d) (CanonicalAuxiliaryCandidateCover.encode d i))=i.1.val := by
  unfold sign
  simp only [pairSnd_pair,pairFst_pair]
  exact CanonicalAuxiliaryCandidateCover.encode_prefix d i

theorem source_encode (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d) :
    source (pair (CanonicalSignRefinement.original d) (CanonicalAuxiliaryCandidateCover.encode d i))=
      CanonicalSignRefinement.source d i.1 := by
  unfold source
  rw [pairFst_pair,sign_encode]
  rfl

theorem candidate_encode (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d) :
    candidate (pair (CanonicalSignRefinement.original d) (CanonicalAuxiliaryCandidateCover.encode d i))=i.2.val := by
  unfold candidate
  rw [source_encode,pairSnd_pair,pairFst_pair]
  exact CanonicalAuxiliaryCandidateCover.encode_candidate d i

theorem padding_encode (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d) :
    padding (pair (CanonicalSignRefinement.original d) (CanonicalAuxiliaryCandidateCover.encode d i))=
      List.replicate (CanonicalAuxiliaryCandidateCover.labelBudget (CanonicalSignRefinement.original d)-i.2.val.length) false := by
  unfold padding
  rw [source_encode,pairSnd_pair,pairFst_pair]
  change ((CanonicalAuxiliaryCandidateCover.encode d i).drop (CanonicalSignRefinement.width d)).drop
    (CanonicalAuxiliaryCandidateCover.width (CanonicalSignRefinement.source d i.1))=_
  have H : ((CanonicalAuxiliaryCandidateCover.encode d i).drop i.1.val.length).drop i.2.val.length=
      List.replicate (CanonicalAuxiliaryCandidateCover.labelBudget (CanonicalSignRefinement.original d)-i.2.val.length) false := by
    unfold CanonicalAuxiliaryCandidateCover.encode
    rw [List.drop_left,List.drop_left]
  simpa only [i.1.property.1,i.2.property] using H

theorem guard_encode (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d) :
    Guard (pair (CanonicalSignRefinement.original d) (CanonicalAuxiliaryCandidateCover.encode d i)) := by
  constructor
  · simp only [pairSnd_pair,pairFst_pair]
    exact CanonicalAuxiliaryCandidateCover.encode_length d i
  · rw [padding_encode,List.count_replicate]
    rfl

noncomputable def candidatePacket (q : List Bool) := pair (source q) (candidate q)
theorem candidatePacket_FP : candidatePacket∈FP := mem_FP_pair source_FP candidate_FP

def Valid (q : List Bool) : Prop := Guard q ∧ source q∈FormulaSignSlotCircuit.language ∧
  AuxiliaryCandidateComponentCover.Good CanonicalAuxiliaryCandidateCover.dimension_unary
    CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope (source q) (candidate q)
def language : Language := {q | Valid q}

theorem valid_encode_iff (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d) :
    Valid (pair (CanonicalSignRefinement.original d) (CanonicalAuxiliaryCandidateCover.encode d i))↔
      AuxiliaryCandidateComponentCover.Good CanonicalAuxiliaryCandidateCover.dimension_unary
        CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope
        (CanonicalSignRefinement.source d i.1) i.2.val := by
  unfold Valid
  rw [source_encode,candidate_encode]
  exact ⟨fun h=>h.2.2,fun h=>⟨guard_encode d i,i.1.property.2,h⟩⟩

theorem encoded_nonempty_iff (d : Description) (hd : d.WellFormed) (i : CanonicalAuxiliaryCandidateCover.Index d) :
    (CanonicalAuxiliaryCandidateCover.piece d i).Nonempty↔
      Valid (pair (CanonicalSignRefinement.original d) (CanonicalAuxiliaryCandidateCover.encode d i)) :=
  (CanonicalAuxiliaryCandidateCover.piece_nonempty_iff_good d hd i).trans (valid_encode_iff d i).symm
end LeanCanny.Connectivity.CanonicalAuxiliaryCandidateLabels

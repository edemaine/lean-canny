/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateWidth
public import LeanCanny.Encoding.BracketsFP
public import LeanCanny.Computation.PSPACEClosure
/-! # Fixed original-width candidate labels with canonical zero vertex padding -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def labelWidth {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (original : List Bool) :=
  adviceWidth n t original+vertexBudget hn ht ha original

noncomputable def vertex {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (q : List Bool) :=
  ((pairSnd q).drop (adviceWidth n t (pairFst q))).take (actualWidth hn ht ha q)

noncomputable def padding {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (q : List Bool) :=
  ((pairSnd q).drop (adviceWidth n t (pairFst q))).drop (actualWidth hn ht ha q)

noncomputable def packet {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (q : List Bool) :=
  pair (source n t q) (vertex hn ht ha q)

def Guard {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (q : List Bool) : Prop :=
  (pairSnd q).length=labelWidth hn ht ha (pairFst q) ∧ (padding hn ht ha q).count true=0

def Valid {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (q : List Bool) : Prop :=
  Guard hn ht ha q ∧ SquareSampleCompleteVertices.Valid (input hn ht ha) (source n t q) (vertex hn ht ha q)

def language {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : Language :=
  {q | Valid hn ht ha q}

theorem labelWidth_unary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    UnaryFn (labelWidth hn ht ha) := (adviceWidth_unary hn ht).add (vertexBudget_unary hn ht ha)

theorem vertex_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : vertex hn ht ha∈FP :=
  take_mem_FP (drop_mem_FP pairSnd_mem_FP ((adviceWidth_unary hn ht).comp pairFst_mem_FP)) (actualWidth_unary hn ht ha)

theorem padding_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : padding hn ht ha∈FP :=
  drop_mem_FP (drop_mem_FP pairSnd_mem_FP ((adviceWidth_unary hn ht).comp pairFst_mem_FP)) (actualWidth_unary hn ht ha)

theorem packet_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : packet hn ht ha∈FP :=
  mem_FP_pair (source_FP hn ht) (vertex_FP hn ht ha)

theorem guard_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : FPPred (Guard hn ht ha) :=
  (FPPred.eq (UnaryFn.length pairSnd_mem_FP) ((labelWidth_unary hn ht ha).comp pairFst_mem_FP)).and
    (FPPred.eq (Brackets.countTrue_unary.comp (padding_FP hn ht ha)) (UnaryFn.const 0))

theorem label_width_polynomial {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    ∃ p : Polynomial ℕ, ∀ original,labelWidth hn ht ha original≤p.eval original.length := by
  obtain ⟨p,hp⟩:=output_length_poly_of_mem_FP (labelWidth_unary hn ht ha).mem_FP
  exact ⟨p,fun original => by simpa only [List.length_replicate] using hp original⟩

theorem decider {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    SpaceDecider (language hn ht ha) := by
  let D := (SquareSampleCompleteVertices.decider (native_access hn ht ha)).precompose
    (packet hn ht ha) (packet_FP hn ht ha)
  have HG := ComputableInPolySpace.of_tidyPolyTime (guard_FP hn ht ha).computable
  have Hfalse := ComputableInPolySpace.of_tidyPolyTime
    (ComputableTidilyInPolyTime.const (encIn:=encBits) (encMid:=encBool) false)
  apply SpaceDecider.of_computable (HG.ite D.computable Hfalse)
  intro q
  change Valid hn ht ha q ↔ (if decide (Guard hn ht ha q) then decide (q∈_) else false)=true
  simp only [Valid,Set.mem_preimage,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,
    packet,pairFst_pair,pairSnd_pair]
  by_cases h : Guard hn ht ha q <;> simp only [h,decide_true,decide_false,ite_true,ite_false,
    true_and,false_and,Bool.false_eq_true,decide_eq_true_eq]

theorem mem_PSPACE {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    language hn ht ha∈PSPACE := (decider hn ht ha).mem_PSPACE
end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate

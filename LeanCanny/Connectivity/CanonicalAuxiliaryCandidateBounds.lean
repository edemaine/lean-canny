/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover

/-! # One original polynomial bounds every sign-piece candidate word

The sign word has native unary width. Composing its packet-length bound with
the actual auxiliary label-width bound gives one polynomial for all accepted
sign pieces of every original Boolean input.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open scoped Classical

theorem width_bound : ∃ p : Polynomial ℕ,∀ d : Description,∀ l : CanonicalSignRefinement.Label d,
    width (CanonicalSignRefinement.source d l)≤p.eval (CanonicalSignRefinement.original d).length := by
  obtain ⟨r,hr⟩:=output_length_poly_of_mem_FP width_unary.mem_FP
  obtain ⟨s,hs⟩:=output_length_poly_of_mem_FP
    (((UnaryFn.const 2).mul ClosedFormulaGateMetadata.count_unary).mem_FP)
  let packetBound : Polynomial ℕ:=2*Polynomial.X+2+s
  refine ⟨r.comp packetBound,fun d l=>?_⟩
  have HS : (CanonicalSignRefinement.width d)≤s.eval (CanonicalSignRefinement.original d).length := by
    simpa only [CanonicalSignRefinement.width,List.length_replicate] using hs (CanonicalSignRefinement.original d)
  have HP : (CanonicalSignRefinement.source d l).length≤packetBound.eval (CanonicalSignRefinement.original d).length := by
    simp only [CanonicalSignRefinement.source,pair_length,l.property.1,packetBound,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega
  have HW : width (CanonicalSignRefinement.source d l)≤r.eval (CanonicalSignRefinement.source d l).length := by
    simpa only [List.length_replicate] using hr (CanonicalSignRefinement.source d l)
  simpa only [Polynomial.eval_comp] using HW.trans (r.eval_mono HP)

noncomputable def labelPolynomial : Polynomial ℕ:=Classical.choose width_bound
noncomputable def labelBudget (original : List Bool) : ℕ:=labelPolynomial.eval original.length

theorem labelBudget_unary : UnaryFn labelBudget :=
  IntegralMixedAuxiliaryCandidate.polynomial_eval_unary _

theorem label_le_budget (d : Description) (l : CanonicalSignRefinement.Label d) :
    width (CanonicalSignRefinement.source d l)≤labelBudget (CanonicalSignRefinement.original d) :=
  Classical.choose_spec width_bound d l

noncomputable def tagWidth (original : List Bool) :=
  2*ClosedFormulaGateMetadata.count original+labelBudget original

theorem tagWidth_unary : UnaryFn tagWidth :=
  ((UnaryFn.const 2).mul ClosedFormulaGateMetadata.count_unary).add labelBudget_unary

noncomputable def encode (d : Description) (i : Index d) : List Bool :=
  i.1.val++(i.2.val++List.replicate (labelBudget (CanonicalSignRefinement.original d)-i.2.val.length) false)

theorem encode_length (d : Description) (i : Index d) :
    (encode d i).length=tagWidth (CanonicalSignRefinement.original d) := by
  have HI : i.2.val.length=width (CanonicalSignRefinement.source d i.1) := i.2.property
  have HL:=label_le_budget d i.1
  simp only [encode,List.length_append,List.length_replicate,i.1.property.1,HI,tagWidth,
    CanonicalSignRefinement.width]
  omega

theorem encode_prefix (d : Description) (i : Index d) :
    (encode d i).take (CanonicalSignRefinement.width d)=i.1.val := by
  have H : (encode d i).take i.1.val.length=i.1.val := List.take_left
  simpa only [i.1.property.1] using H

theorem encode_candidate (d : Description) (i : Index d) :
    ((encode d i).drop (CanonicalSignRefinement.width d)).take (width (CanonicalSignRefinement.source d i.1))=i.2.val := by
  have H : ((encode d i).drop i.1.val.length).take i.2.val.length=i.2.val := by
    unfold encode
    rw [List.drop_left,List.take_left]
  simpa only [i.1.property.1,i.2.property] using H

theorem encode_injective (d : Description) : Function.Injective (encode d) := by
  rintro ⟨l,i⟩ ⟨k,j⟩ H
  have HP:=congrArg (fun w : List Bool=>w.take (CanonicalSignRefinement.width d)) H
  have HK : l=k:=Subtype.ext ((encode_prefix d ⟨l,i⟩).symm.trans (HP.trans (encode_prefix d ⟨k,j⟩)))
  cases HK
  have HC:=congrArg (fun w : List Bool=>(w.drop (CanonicalSignRefinement.width d)).take
    (width (CanonicalSignRefinement.source d l))) H
  have HI : i=j:=Subtype.ext ((encode_candidate d ⟨l,i⟩).symm.trans (HC.trans (encode_candidate d ⟨l,j⟩)))
  cases HI
  rfl

noncomputable def vertex (d : Description) (i : Index d) : Vertex (tagWidth (CanonicalSignRefinement.original d)) :=
  ⟨encode d i,encode_length d i⟩

theorem index_card_le (d : Description) :
    Nat.card (Index d)≤2^tagWidth (CanonicalSignRefinement.original d) := by
  have HI : Function.Injective (vertex d) := by
    intro i j H
    exact encode_injective d (congrArg (fun v : Vertex (tagWidth (CanonicalSignRefinement.original d))=>v.val) H)
  exact (Nat.card_le_card_of_injective (vertex d) HI).trans (SampledBitComponentCover.vertex_card_le _)

end LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover

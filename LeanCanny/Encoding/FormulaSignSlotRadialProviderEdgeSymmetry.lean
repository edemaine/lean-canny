/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderEdge
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignatureReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIdentityReadback
/-! # Actual native provider edges can be traversed in either direction -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignature
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "D" => FormulaSignSlotRadialProviderAtomic.dimension
local notation "S" => FormulaSignSlotRadialProviderAtomic.input

private theorem field_packet_symm (cL wL cR wR : List Bool)
    (hL : SquareSampleCompleteVertices.Valid S cL wL) (hR : SquareSampleCompleteVertices.Valid S cR wR)
    (a b : ℕ) (H : FormulaSignSlotRadialProviderFieldEquality.packet cL wL cR wR a b∈
      FormulaSignSlotRadialProviderFieldEquality.language) :
    FormulaSignSlotRadialProviderFieldEquality.packet cR wR cL wL b a∈FormulaSignSlotRadialProviderFieldEquality.language := by
  have HB : a<FormulaSignSlotRadialProviderFieldEquality.count cL ∧
      b<FormulaSignSlotRadialProviderFieldEquality.count cR := by
    simpa only [FormulaSignSlotRadialProviderFieldEquality.Labels,
      FormulaSignSlotRadialProviderFieldEquality.context,FormulaSignSlotRadialProviderFieldEquality.sample,
      FormulaSignSlotRadialProviderFieldEquality.label,FormulaSignSlotRadialProviderFieldEquality.labelWord,
      FormulaSignSlotRadialProviderFieldEquality.packet,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using H.2.2.2.1
  exact (FormulaSignSlotRadialProviderFieldEquality.language_packet_iff cR wR cL wL hR hL b a HB.2 HB.1).mpr
    ((FormulaSignSlotRadialProviderFieldEquality.agrees_iff cL wL cR wR hL hR a b).mp H.2.2.2.2).symm

attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.Valid
  FormulaSignSlotRadialProviderRecordPlan.bank ownSignature table query

theorem language_symm (a b : List Bool) (ha : A a) (hb : A b) (H : pair a b∈language) : pair b a∈language := by
  have HC : D a=D b ∧ FormulaSignSlotRadialProviderAtomic.depth a=FormulaSignSlotRadialProviderAtomic.depth b ∧
      0<FormulaSignSlotRadialProviderAtomic.depth a := by
    simpa only [Compatible,left,right,pairFst_pair,pairSnd_pair] using H.1
  refine ⟨?_,?_⟩
  · simpa only [Compatible,left,right,pairFst_pair,pairSnd_pair] using
      And.intro HC.1.symm (And.intro HC.2.1.symm (HC.2.1 ▸ HC.2.2))
  · have HL := H.2
    unfold query at HL ⊢
    simp only [left,right,pairFst_pair,pairSnd_pair] at HL ⊢
    refine ⟨?_,?_,?_⟩
    · simpa only [FormulaSignSlotRadialProviderFieldEquality.context,FormulaSignSlotRadialProviderFieldEquality.word,
        FormulaSignSlotRadialProviderFieldEquality.sample,FormulaSignSlotRadialProviderFieldEqualityList.packet,
        Bool.false_eq_true,ite_false,pairFst_pair,pairSnd_pair] using FormulaSignSlotRadialProviderAtomic.full_valid b hb
    · simpa only [FormulaSignSlotRadialProviderFieldEquality.context,FormulaSignSlotRadialProviderFieldEquality.word,
        FormulaSignSlotRadialProviderFieldEquality.sample,FormulaSignSlotRadialProviderFieldEqualityList.packet,
        ite_true,pairFst_pair,pairSnd_pair] using FormulaSignSlotRadialProviderAtomic.full_valid a ha
    · intro i hi
      have HI : i<D b+2 := by
        simpa only [FormulaSignSlotRadialProviderFieldEqualityList.count,FormulaSignSlotRadialProviderFieldEqualityList.table,
          FormulaSignSlotRadialProviderFieldEqualityList.packet,pairSnd_pair,table_pair_count] using hi
      have HIA : i<D a+2 := by omega
      have HP := HL.2.2 i (by
        simpa only [FormulaSignSlotRadialProviderFieldEqualityList.count,FormulaSignSlotRadialProviderFieldEqualityList.table,
          FormulaSignSlotRadialProviderFieldEqualityList.packet,pairSnd_pair,table_pair_count] using HIA)
      rw [FormulaSignSlotRadialProviderFieldEqualityList.query_packet,table_pair_lookup a b ⟨i,HIA⟩] at HP
      rw [FormulaSignSlotRadialProviderFieldEqualityList.query_packet,table_pair_lookup b a ⟨i,HI⟩]
      simp only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair] at HP ⊢
      exact field_packet_symm _ _ _ _ (FormulaSignSlotRadialProviderAtomic.full_valid a ha)
        (FormulaSignSlotRadialProviderAtomic.full_valid b hb) _ _ HP
end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignature

namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderEdge
open LeanCanny.Algebra LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

theorem symm {a b : List Bool} (H : Adjacent a b) : Adjacent b a := by
  obtain ⟨ha,hb⟩ := valid a b H
  have HC := provider_eq a b H
  rcases H with HI|HP
  · exact Or.inl ((FormulaSignSlotRadialProviderIdentity.language_iff b a hb ha HC.symm).mpr
      (((FormulaSignSlotRadialProviderIdentity.language_iff a b ha hb HC).mp HI).symm))
  · have HL : FormulaSignSlotRadialProviderLocalEdge.Local a := by simpa only [pairFst_pair] using HP.2.1
    have HR : FormulaSignSlotRadialProviderLocalEdge.Local b := by simpa only [pairSnd_pair] using HP.2.2.1
    refine Or.inr ⟨?_,?_,?_,FormulaSignSlotRadialProviderProperMidSignature.language_symm a b ha hb HP.2.2.2⟩
    · simpa only [FormulaSignSlotRadialProviderIdentity.SameProvider,FormulaSignSlotRadialProviderIdentity.left,
        FormulaSignSlotRadialProviderIdentity.right,pairFst_pair,pairSnd_pair] using HC.symm
    · simpa only [pairFst_pair] using HR
    · simpa only [pairSnd_pair] using HL
end LeanCanny.Encoding.FormulaSignSlotRadialProviderEdge

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignatureReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicPoint
/-! # Accepted midpoint signatures compare actual original chronological fields -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignature
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "D" => FormulaSignSlotRadialProviderAtomic.dimension
local notation "S" => FormulaSignSlotRadialProviderAtomic.input
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables

private theorem native_fields_eq (cL wL cR wR : List Bool)
    (hL : SquareSampleCompleteVertices.Valid S cL wL) (hR : SquareSampleCompleteVertices.Valid S cR wR)
    (a b : ℕ) (H : FormulaSignSlotRadialProviderFieldEquality.packet cL wL cR wR a b∈
      FormulaSignSlotRadialProviderFieldEquality.language) :
    FormulaSignSlotRadialProviderAtomic.bankField cL wL hL a=
      FormulaSignSlotRadialProviderAtomic.bankField cR wR hR b := by
  have HE := (FormulaSignSlotRadialProviderFieldEquality.agrees_iff cL wL cR wR hL hR a b).mp H.2.2.2.2
  have HB : a<FormulaSignSlotRadialProviderFieldEquality.count cL ∧
      b<FormulaSignSlotRadialProviderFieldEquality.count cR := by
    simpa only [FormulaSignSlotRadialProviderFieldEquality.Labels,
      FormulaSignSlotRadialProviderFieldEquality.context,FormulaSignSlotRadialProviderFieldEquality.sample,
      FormulaSignSlotRadialProviderFieldEquality.label,FormulaSignSlotRadialProviderFieldEquality.labelWord,
      FormulaSignSlotRadialProviderFieldEquality.packet,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using H.2.2.2.1
  rw [FormulaSignSlotRadialProviderFieldEquality.point_env cL wL hL a HB.1,
    FormulaSignSlotRadialProviderFieldEquality.point_env cR wR hR b HB.2] at HE
  exact HE

noncomputable def signatureValue (q : List Bool) (hv : A q) (i : ℕ) :=
  FormulaSignSlotRadialProviderAtomic.field q hv (Nat.fromBitsLE (WordList.get (ownSignature q) i))

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  FormulaSignSlotRadialProviderRecordPlan.parameters FormulaSignSlotRadialProviderAtomic.Valid
  FormulaSignSlotRadialProviderAtomic.dimension signatureValue ownSignature table query

theorem language_values (a b : List Bool) (ha : A a) (hb : A b)
    (H : pair a b∈language) (i : ℕ) (hi : i<D a+2) : signatureValue a ha i=signatureValue b hb i := by
  have HL := H.2
  unfold query at HL
  simp only [left,right,pairFst_pair,pairSnd_pair] at HL
  have HI : i<WordListRecords.count (table (pair a b)) := by rw [table_pair_count];exact hi
  have HP := HL.2.2 i (by
    simpa only [FormulaSignSlotRadialProviderFieldEqualityList.count,
      FormulaSignSlotRadialProviderFieldEqualityList.table,FormulaSignSlotRadialProviderFieldEqualityList.packet,
      pairSnd_pair] using HI)
  rw [FormulaSignSlotRadialProviderFieldEqualityList.query_packet,table_pair_lookup a b ⟨i,hi⟩] at HP
  simp only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
    pairFst_pair,pairSnd_pair] at HP
  unfold signatureValue FormulaSignSlotRadialProviderAtomic.field
  exact native_fields_eq _ _ _ _ (FormulaSignSlotRadialProviderAtomic.full_valid a ha)
    (FormulaSignSlotRadialProviderAtomic.full_valid b hb) _ _ HP

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignature

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIdentityLayout
/-! # Native identity is equality of the complete actual atomic point

The words and histories may differ. Every scalar comparison is discharged
by the accepted vertex's actual coordinate receipt.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderIdentity
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
 FormulaSignSlotRadialProviderRecordPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 FormulaSignSlotRadialProviderAtomic.point IntegralFramedPhysicalSquare.point

noncomputable def point (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) : Fin (D q+1)→ℝ:=fun i=>
  FormulaSignSlotRadialProviderAtomic.point q hv
    (Fin.cast (congrArg (·+1) (FormulaSignSlotRadialProviderAtomic.native_dimension q)).symm i)

theorem signature_bound (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (i : Fin (D q+1)) :
    Nat.fromBitsLE (WordList.get (ownSignature q) i.val)<
      FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context q) := by
  simpa only [ownSignature,Fin.val_cast,FormulaSignSlotRadialProviderFieldEquality.count,
    IntegralMixedFramedHistoryFamilyBits.family_birth] using
    FormulaSignSlotRadialProviderAtomic.signature_bounded q hv
      (Fin.cast (congrArg (·+1) (FormulaSignSlotRadialProviderAtomic.native_dimension q)).symm i)

theorem signature_point (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (i : Fin (D q+1)) :
    FormulaSignSlotRadialProviderFieldEquality.point
      (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q)
      (FormulaSignSlotRadialProviderAtomic.full_valid q hv)
      (Nat.fromBitsLE (WordList.get (ownSignature q) i.val))=point q hv i := by
  rw [FormulaSignSlotRadialProviderFieldEquality.point_env _ _ _ _ (signature_bound q hv i)]
  simpa only [ownSignature,point,FormulaSignSlotRadialProviderAtomic.field,Fin.val_cast] using
    FormulaSignSlotRadialProviderAtomic.signature_readback q hv
      (Fin.cast (congrArg (·+1) (FormulaSignSlotRadialProviderAtomic.native_dimension q)).symm i)

theorem table_pair_count (a b : List Bool) :WordListRecords.count (table (pair a b))=D a+1 :=by
  unfold table
  rw [IntegralMixedPhysicalPointSignatureComparison.pairs_count]
  simp only [left,pairFst_pair]

theorem table_pair_lookup (a b : List Bool) (i : Fin (D a+1)) :
    WordList.get (table (pair a b)) i.val=
      pair (WordList.get (ownSignature a) i.val) (WordList.get (ownSignature b) i.val) :=by
  unfold table
  simp only [left,right,pairFst_pair,pairSnd_pair]
  exact IntegralMixedPhysicalPointSignatureComparison.pairs_lookup _ _ _ i

private theorem fin_heq_iff {a b : ℕ} (H : a=b) (p : Fin a→ℝ) (q : Fin b→ℝ) :
    HEq p q↔∀i,p i=q (Fin.cast H i) :=by
  cases H
  constructor
  · intro HE i
    exact congrFun (eq_of_heq HE) i
  · intro HE
    exact heq_of_eq (funext HE)

attribute [local irreducible] point ownSignature table query
 FormulaSignSlotRadialProviderFieldEquality.point FormulaSignSlotRadialProviderFieldEquality.count
 FormulaSignSlotRadialProviderAtomic.context FormulaSignSlotRadialProviderAtomic.word FormulaSignSlotRadialProviderAtomic.Valid
 IntegralFramedPhysicalSquare.input

theorem query_iff (a b : List Bool) (hA : FormulaSignSlotRadialProviderAtomic.Valid a)
    (hB : FormulaSignSlotRadialProviderAtomic.Valid b) (hd : D a=D b) :
    query (pair a b)∈FormulaSignSlotRadialProviderFieldEqualityList.language ↔
      HEq (point a hA) (point b hB) :=by
  let Hdim:=congrArg (·+1) hd
  have HB : ∀i<WordListRecords.count (table (pair a b)),
      FormulaSignSlotRadialProviderFieldEqualityList.label false (WordList.get (table (pair a b)) i)<
        FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context a) ∧
      FormulaSignSlotRadialProviderFieldEqualityList.label true (WordList.get (table (pair a b)) i)<
        FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context b):=by
    intro i hi
    rw [table_pair_count a b] at hi
    rw [table_pair_lookup a b ⟨i,hi⟩]
    simp only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair]
    exact ⟨signature_bound a hA ⟨i,hi⟩,
      signature_bound b hB (Fin.cast Hdim ⟨i,hi⟩)⟩
  unfold query
  simp only [left,right,pairFst_pair,pairSnd_pair]
  rw [FormulaSignSlotRadialProviderFieldEqualityList.language_packet_iff
    _ _ _ _ _ (FormulaSignSlotRadialProviderAtomic.full_valid a hA)
      (FormulaSignSlotRadialProviderAtomic.full_valid b hB) HB,
    fin_heq_iff Hdim]
  constructor
  · intro HE i
    have H:=HE i.val (by rw [table_pair_count a b];exact i.isLt)
    rw [table_pair_lookup a b i] at H
    simp only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair] at H
    exact (signature_point a hA i).symm.trans
      (H.trans (signature_point b hB (Fin.cast Hdim i)))
  · intro HE i hi
    rw [table_pair_count a b] at hi
    rw [table_pair_lookup a b ⟨i,hi⟩]
    simp only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair]
    exact (signature_point a hA ⟨i,hi⟩).trans
      ((HE ⟨i,hi⟩).trans (signature_point b hB (Fin.cast Hdim ⟨i,hi⟩)).symm)

theorem language_iff (a b : List Bool) (hA : FormulaSignSlotRadialProviderAtomic.Valid a)
    (hB : FormulaSignSlotRadialProviderAtomic.Valid b)
    (hc : FormulaSignSlotRadialProviderAtomic.provider a=FormulaSignSlotRadialProviderAtomic.provider b) :
    pair a b∈language ↔HEq (point a hA) (point b hB) :=by
  have HD:=dimension_eq_of_providers a b hc
  simpa only [language,Set.mem_ofPred_eq,SameProvider,left,right,pairFst_pair,pairSnd_pair,hc,hA,hB,true_and]
    using query_iff a b hA hB HD

end LeanCanny.Encoding.FormulaSignSlotRadialProviderIdentity

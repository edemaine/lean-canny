/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapIdentityLayout
/-! # Native identity is equality of the complete actual atomic point

The words and histories may differ. Every scalar comparison is discharged
by the accepted vertex's actual coordinate receipt.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapIdentity
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
 IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapAtomic.point IntegralFramedPhysicalSquare.point

noncomputable def point (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) : Fin (D q+1)→ℝ:=fun i=>
  IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv
    (Fin.cast (congrArg (·+1) (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q)).symm i)

theorem signature_point (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (i : Fin (D q+1)) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv)
      (Nat.fromBitsLE (WordList.get (ownSignature hn ht ha hR0 q) i.val))=point hn ht ha hR0 q hv i :=by
  simpa only [ownSignature,point,Fin.val_cast] using IntegralMixedRoadmapAtomic.signature_readback hn ht ha hR0 q hv
    (Fin.cast (congrArg (·+1) (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q)).symm i)

theorem signature_bound (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (i : Fin (D q+1)) :
    Nat.fromBitsLE (WordList.get (ownSignature hn ht ha hR0 q) i.val)<
      IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context q) :=by
  simpa only [ownSignature,Fin.val_cast] using IntegralMixedRoadmapAtomic.signature_bounded hn ht ha hR0 q hv
    (Fin.cast (congrArg (·+1) (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q)).symm i)

theorem table_pair_count (a b : List Bool) :WordListRecords.count (table hn ht ha hR0 (pair a b))=D a+1 :=by
  unfold table
  rw [IntegralMixedPhysicalPointSignatureComparison.pairs_count]
  simp only [left,pairFst_pair]

theorem table_pair_lookup (a b : List Bool) (i : Fin (D a+1)) :
    WordList.get (table hn ht ha hR0 (pair a b)) i.val=
      pair (WordList.get (ownSignature hn ht ha hR0 a) i.val) (WordList.get (ownSignature hn ht ha hR0 b) i.val) :=by
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
 IntegralMixedPhysicalFieldEquality.point IntegralMixedPhysicalFieldEquality.count
 IntegralMixedRoadmapAtomic.context IntegralMixedRoadmapAtomic.word IntegralMixedRoadmapAtomic.Valid
 IntegralFramedPhysicalSquare.input

theorem query_iff (a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b) (hd : D a=D b) :
    query hn ht ha hR0 (pair a b)∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0) ↔
      HEq (point hn ht ha hR0 a hA) (point hn ht ha hR0 b hB) :=by
  let Hdim:=congrArg (·+1) hd
  have HB : ∀i<WordListRecords.count (table hn ht ha hR0 (pair a b)),
      IntegralMixedPhysicalFieldEqualityList.label false (WordList.get (table hn ht ha hR0 (pair a b)) i)<
        IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context a) ∧
      IntegralMixedPhysicalFieldEqualityList.label true (WordList.get (table hn ht ha hR0 (pair a b)) i)<
        IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context b):=by
    intro i hi
    rw [table_pair_count hn ht ha hR0 a b] at hi
    rw [table_pair_lookup hn ht ha hR0 a b ⟨i,hi⟩]
    simp only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair]
    exact ⟨signature_bound hn ht ha hR0 a hA ⟨i,hi⟩,
      signature_bound hn ht ha hR0 b hB (Fin.cast Hdim ⟨i,hi⟩)⟩
  unfold query
  simp only [left,right,pairFst_pair,pairSnd_pair]
  rw [IntegralMixedPhysicalFieldEqualityList.language_packet_iff hn ht ha (radius_binary hR0)
    _ _ _ _ _ (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 a hA)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 b hB) HB,
    fin_heq_iff Hdim]
  constructor
  · intro HE i
    have H:=HE i.val (by rw [table_pair_count hn ht ha hR0 a b];exact i.isLt)
    rw [table_pair_lookup hn ht ha hR0 a b i] at H
    simp only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair] at H
    exact (signature_point hn ht ha hR0 a hA i).symm.trans
      (H.trans (signature_point hn ht ha hR0 b hB (Fin.cast Hdim i)))
  · intro HE i hi
    rw [table_pair_count hn ht ha hR0 a b] at hi
    rw [table_pair_lookup hn ht ha hR0 a b ⟨i,hi⟩]
    simp only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair]
    exact (signature_point hn ht ha hR0 a hA ⟨i,hi⟩).trans
      ((HE ⟨i,hi⟩).trans (signature_point hn ht ha hR0 b hB (Fin.cast Hdim ⟨i,hi⟩)).symm)

theorem language_iff (a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc : IntegralMixedRoadmapAtomic.candidate a=IntegralMixedRoadmapAtomic.candidate b) :
    pair a b∈language hn ht ha hR0 ↔HEq (point hn ht ha hR0 a hA) (point hn ht ha hR0 b hB) :=by
  have HD:=dimension_eq_of_candidates hn ht ha hR0 a b hc
  simpa only [language,Set.mem_ofPred_eq,SameCandidate,left,right,pairFst_pair,pairSnd_pair,hc,hA,hB,true_and]
    using query_iff hn ht ha hR0 a b hA hB HD

end LeanCanny.Encoding.IntegralMixedRoadmapIdentity

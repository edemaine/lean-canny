/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicSignature
/-! # Every field of the native paired midpoint signature

The final field retains the right endpoint separately from the left endpoint
used in the height slot. All other fields are literal frozen or MID captures.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem signature_encode (n initial : ℕ) (q : List Bool) :
    signature n initial q=WordList.encode
      (((List.range (n+1)).map (fun i=>BinaryNatCode.encode
        (IntegralMixedChronologicalPointSignatureCode.producer n
          (IntegralMixedRoadmapProper.midFirst n initial q) (extendedLabels q) i)))++
        [BinaryNatCode.encode (IntegralMixedRoadmapProper.producer true q)]) :=by
  unfold signature IntegralMixedChronologicalPointSignatureCode.code
  rw [IntegralMixedRoadmapLevel.encode_append]
  rfl

theorem signature_lookup (n initial : ℕ) (q : List Bool) (i : ℕ) (hi : i < n+1) :
    Nat.fromBitsLE (WordList.get (signature n initial q) i)=
      IntegralMixedChronologicalPointSignatureCode.producer n
        (IntegralMixedRoadmapProper.midFirst n initial q) (extendedLabels q) i :=by
  rw [signature_encode,WordList.get_encode,List.getElem?_append_left (by simp only [List.length_map,List.length_range];exact hi)]
  simp only [List.getElem?_map,List.getElem?_range hi,Option.map_some,Option.getD_some,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem signature_lookup_right (n initial : ℕ) (q : List Bool) :
    Nat.fromBitsLE (WordList.get (signature n initial q) (n+1))=IntegralMixedRoadmapProper.producer true q :=by
  rw [signature_encode,WordList.get_encode,List.getElem?_append_right (by simp only [List.length_map,List.length_range];omega)]
  simp only [List.length_map,List.length_range,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem signature_lookup_frozen (n initial : ℕ) (q : List Bool) (i : ℕ)
    (hi : i<IntegralMixedRoadmapProper.levelIndex q) (hn : IntegralMixedRoadmapProper.levelIndex q ≤ n) :
    Nat.fromBitsLE (WordList.get (signature n initial q) i)=
      Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProper.labels q) i) :=by
  rw [signature_lookup n initial q i (by omega)]
  unfold IntegralMixedChronologicalPointSignatureCode.producer extendedLabels
  rw [IntegralMixedChronologicalEndpointCode.append_count,IntegralMixedRoadmapProper.labels_count,
    ite_eq_left (by omega)]
  exact IntegralMixedChronologicalEndpointCode.append_lookup_old _ _ i (by rw [IntegralMixedRoadmapProper.labels_count];exact hi)

theorem signature_lookup_left (n initial : ℕ) (q : List Bool)
    (hn : IntegralMixedRoadmapProper.levelIndex q ≤ n) :
    Nat.fromBitsLE (WordList.get (signature n initial q) (IntegralMixedRoadmapProper.levelIndex q))=
      IntegralMixedRoadmapProper.producer false q :=by
  rw [signature_lookup n initial q _ (by omega)]
  unfold IntegralMixedChronologicalPointSignatureCode.producer extendedLabels
  rw [IntegralMixedChronologicalEndpointCode.append_count,IntegralMixedRoadmapProper.labels_count,
    ite_eq_left (by omega),←IntegralMixedRoadmapProper.labels_count q]
  exact IntegralMixedChronologicalEndpointCode.append_lookup_last _ _

theorem signature_lookup_free (n initial : ℕ) (q : List Bool) (i : ℕ)
    (hi : IntegralMixedRoadmapProper.levelIndex q < i) (hin : i ≤ n) :
    Nat.fromBitsLE (WordList.get (signature n initial q) i)=
      IntegralMixedRoadmapProper.midProducer n initial q i :=by
  rw [signature_lookup n initial q i (by omega)]
  unfold IntegralMixedChronologicalPointSignatureCode.producer extendedLabels
  rw [IntegralMixedChronologicalEndpointCode.append_count,IntegralMixedRoadmapProper.labels_count,ite_eq_right (by omega)]
  unfold IntegralMixedRoadmapProper.midProducer
  omega


variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
open IntegralMixedOriginalRegularSource (radius_binary)
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
 IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapAtomic.context IntegralMixedRoadmapAtomic.word IntegralMixedRoadmapAtomic.Valid
 IntegralFramedPhysicalSquare.input IntegralMixedPhysicalFieldEquality.point

theorem table_pair_count (a b : List Bool) :
    WordListRecords.count (table hn ht ha hR0 (pair a b))=D a+2 :=by
  unfold table
  rw [IntegralMixedPhysicalPointSignatureComparison.pairs_count]
  simp only [left,pairFst_pair,Nat.add_assoc]

theorem table_pair_lookup (a b : List Bool) (i : Fin (D a+2)) :
    WordList.get (table hn ht ha hR0 (pair a b)) i.val=
      pair (WordList.get (ownSignature hn ht ha hR0 a) i.val)
        (WordList.get (ownSignature hn ht ha hR0 b) i.val) :=by
  unfold table
  simp only [left,right,pairFst_pair,pairSnd_pair]
  exact IntegralMixedPhysicalPointSignatureComparison.pairs_lookup _ _ _ i

attribute [local irreducible] ownSignature table query

theorem language_values (a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b) (H : pair a b∈language hn ht ha hR0)
    (i : ℕ) (hi : i < D a+2) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (IntegralMixedRoadmapAtomic.context a) (IntegralMixedRoadmapAtomic.word a)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 a hA)
      (Nat.fromBitsLE (WordList.get (ownSignature hn ht ha hR0 a) i))=
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (IntegralMixedRoadmapAtomic.context b) (IntegralMixedRoadmapAtomic.word b)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 b hB)
      (Nat.fromBitsLE (WordList.get (ownSignature hn ht ha hR0 b) i)) :=by
  have HL:=H.2
  unfold query at HL
  simp only [left,right,pairFst_pair,pairSnd_pair] at HL
  have HI : i < WordListRecords.count (table hn ht ha hR0 (pair a b)):=by
    rw [table_pair_count];exact hi
  have HP:=HL.2.2 i (by
    simpa only [IntegralMixedPhysicalFieldEqualityList.count,IntegralMixedPhysicalFieldEqualityList.table,
      IntegralMixedPhysicalFieldEqualityList.packet,pairSnd_pair] using HI)
  rw [IntegralMixedPhysicalFieldEqualityList.query_packet,table_pair_lookup hn ht ha hR0 a b ⟨i,hi⟩] at HP
  simp only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
    pairFst_pair,pairSnd_pair] at HP
  exact (IntegralMixedPhysicalFieldEquality.agrees_iff hn ht ha (radius_binary hR0) _ _ _ _
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 a hA)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 b hB) _ _).mp HP.2.2.2.2

end LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature

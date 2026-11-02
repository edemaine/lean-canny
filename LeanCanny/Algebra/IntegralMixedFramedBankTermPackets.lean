/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankTermSource
public import LeanCanny.Algebra.IndexedKroneckerReader
/-! # Native original-term coordinate coefficient packets -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankTermBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey packet)
open scoped Classical

def queriedIndex (z : List Bool) := Nat.fromBitsLE (IndexedKroneckerReader.coordinate z)
theorem queriedIndex_binary : BinaryFn queriedIndex := BinaryFn.fromBits IndexedKroneckerReader.coordinate_FP
def queriedDegree (z : List Bool) := Nat.fromBitsLE (IndexedKroneckerReader.degreeWord z)
theorem queriedDegree_binary : BinaryFn queriedDegree := BinaryFn.fromBits IndexedKroneckerReader.degreeWord_FP

noncomputable def numeratorPacket (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :=
  packet (IndexedKroneckerReader.context z) (pairSnd z)
    (reverseIndex P D H (IndexedKroneckerReader.context z) (queriedIndex z)) (queriedDegree z)

theorem numeratorPacket_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    numeratorPacket P D H∈FP := by
  have HC : BinaryFn (fun z => (atKey P D H (IndexedKroneckerReader.context z)).count) :=
    (BinaryFn.ofUnary (IntegralMixedFramedBankSnapshotBits.count_unary P a D H)).comp IndexedKroneckerReader.context_FP
  have HR : BinaryFn (fun z => reverseIndex P D H (IndexedKroneckerReader.context z) (queriedIndex z)) :=
    (HC.sub (BinaryFn.const 1)).sub queriedIndex_binary
  exact mem_FP_pair (mem_FP_pair IndexedKroneckerReader.context_FP pairSnd_mem_FP)
    (mem_FP_pair HR.bits_mem_FP queriedDegree_binary.bits_mem_FP)

def denominatorPacket (z : List Bool) := packet (IndexedKroneckerReader.context z) (pairSnd z) 0 0
theorem denominatorPacket_FP : denominatorPacket∈FP :=
  mem_FP_pair (mem_FP_pair IndexedKroneckerReader.context_FP pairSnd_mem_FP)
    (constFn_mem_FP (pair (BinaryNatCode.encode 0) (BinaryNatCode.encode 0)))

noncomputable def coefficientWidth (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (q : List Bool) := width P D H word (PaddedIntegralGeneratorSource.base q)
theorem coefficientWidth_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (hw : word∈FP) : UnaryFn (coefficientWidth P D H word) :=
  (width_unary P a D H word hw).comp PaddedIntegralGeneratorSource.base_FP

noncomputable def active (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) : Prop :=
  queriedIndex z<(atKey P D H (IndexedKroneckerReader.context z)).count
theorem active_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) : FPPred (active P D H) :=
  queriedIndex_binary.lt ((BinaryFn.ofUnary (IntegralMixedFramedBankSnapshotBits.count_unary P a D H)).comp IndexedKroneckerReader.context_FP)

theorem numeratorPacket_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (i k : ℕ) (mw : List Bool) :
    numeratorPacket P D H (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) mw)=
      packet c mw (reverseIndex P D H c i) k := by
  simp only [numeratorPacket,queriedIndex,queriedDegree,IndexedKroneckerReader.context,
    IndexedKroneckerReader.coordinate,IndexedKroneckerReader.degreeWord,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem count_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c mw : List Bool) (i k : ℕ) :
    IntegralMixedFramedBankDenominatorBits.count P D H (packet c mw i k)=(atKey P D H c).count :=
  congrArg (fun key => (atKey P D H key).count) (IntegralMixedFramedBankSnapshotBits.packet_base c mw i k)

theorem index_packet (c mw : List Bool) (i k : ℕ) : IntegralMixedFramedBankDenominatorBits.index (packet c mw i k)=i := by
  simp only [IntegralMixedFramedBankDenominatorBits.index,packet,PaddedIntegralGeneratorSource.row,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem reverse_lt (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (i : ℕ) (hi : i<(atKey P D H c).count) : reverseIndex P D H c i<(atKey P D H c).count := by
  unfold reverseIndex
  omega

theorem reverse_reverse (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (i : ℕ) (hi : i<(atKey P D H c).count) :
    (atKey P D H c).count-1-reverseIndex P D H c i=i := by
  unfold reverseIndex
  omega

end LeanCanny.Algebra.IntegralMixedFramedBankTermBits

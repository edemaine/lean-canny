/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankTermPackets
/-! # Exact original-term coordinate packets retain the joint prefix powers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankTermBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey packet)
open scoped Classical

theorem weight_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c mw : List Bool) (i k : ℕ) (hi : i<(atKey P D H c).count) :
    IntegralMixedFramedBankCoordinateBits.weight P D H (packet c mw (reverseIndex P D H c i) k)=
      UniformIntegralPowerSchedule.birth (P.cap (pairFst c)+1) (2^P.width (pairFst c)) i := by
  have HR := reverse_lt P D H c i hi
  have HX : Nat.fromBitsLE (PaddedIntegralGeneratorSource.row (packet c mw (reverseIndex P D H c i) k))=
      reverseIndex P D H c i := index_packet _ _ _ _
  have HS : IntegralMixedFramedBankCoordinateBits.horizon P (packet c mw (reverseIndex P D H c i) k)=P.cap (pairFst c)+1 := by
    simp only [IntegralMixedFramedBankCoordinateBits.horizon,IntegralMixedFramedCompanionQueryBits.root,
      PaddedIntegralGeneratorSource.base,packet,pairFst_pair]
  have HN : IntegralMixedFramedBankCoordinateBits.scalarDegree P (packet c mw (reverseIndex P D H c i) k)=2^P.width (pairFst c) := by
    simp only [IntegralMixedFramedBankCoordinateBits.scalarDegree,IntegralMixedFramedCompanionQueryBits.root,
      PaddedIntegralGeneratorSource.base,packet,pairFst_pair]
  simp only [IntegralMixedFramedBankCoordinateBits.weight,UniformIntegralPowerSchedule.power,UniformIntegralPowerSchedule.age,
    pairFst_pair,pairSnd_pair,HX,count_packet,HS,HN,min_eq_left HR.le,reverse_reverse P D H c i hi]

theorem encodedDegree_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (c mw : List Bool) (i k : ℕ) (hi : i<(atKey P D H c).count) :
    IntegralMixedFramedBankCoordinateBits.encodedDegree P D H (coefficientWidth P D H word)
      (packet c mw (reverseIndex P D H c i) k)=
      UniformIntegralPowerSchedule.birth (P.cap (pairFst c)+1) (2^P.width (pairFst c)) i*
        2^(reverseIndex P D H c i*width P D H word c) := by
  unfold IntegralMixedFramedBankCoordinateBits.encodedDegree IntegralMixedFramedBankCoordinateBits.clippedIndex
  rw [weight_packet P D H c mw i k hi,index_packet,count_packet,min_eq_left (reverse_lt P D H c i hi).le]
  rw [coefficientWidth,IntegralMixedFramedBankSnapshotBits.packet_base]

theorem coordinate_coefficient_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (c : List Bool) (i k m : ℕ) (hi : i<(atKey P D H c).count) (hm : 0<m) :
    IntegralMixedFramedBankCoordinateBits.coefficient P D H (coefficientWidth P D H word)
      (packet c (BinaryNatCode.encode (m-1)) (reverseIndex P D H c i) k)=
      MatrixPower.residueBits (((numerator P D H word c i).coeff k : ℤ) : ZMod m) := by
  let q := packet c (BinaryNatCode.encode (m-1)) (reverseIndex P D H c i) k
  have HR : IntegralMixedFramedBankDenominatorBits.index q<IntegralMixedFramedBankDenominatorBits.count P D H q := by
    dsimp only [q]
    rw [index_packet,count_packet]
    exact reverse_lt P D H c i hi
  have HE : ((FixedWidthKronecker.encode (IntegralMixedFramedBankDenominatorBits.count P D H q)
      (coefficientWidth P D H word q) (IntegralMixedFramedBankCoordinateBits.polynomial P D H q)).coeff
      (Nat.fromBitsLE (PaddedIntegralGeneratorSource.col q)))=(numerator P D H word c i).coeff k := by
    rw [IntegralMixedFramedBankCoordinateBits.encoded_polynomial,ite_eq_left HR]
    dsimp only [q]
    rw [encodedDegree_packet P D H word c _ i k hi,IntegralMixedFramedBankSnapshotBits.cofactor_packet]
    unfold numerator
    rw [ite_eq_left hi]
    simp only [packet,PaddedIntegralGeneratorSource.col,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HM : IntegralMixedFramedCompanionQueryBits.callerModulus q=m := by
    simp only [q,IntegralMixedFramedCompanionQueryBits.callerModulus,packet,PaddedIntegralGeneratorSource.modulus,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,Nat.sub_add_cancel hm]
  exact congrArg₂ (fun (a : ℤ) (M : ℕ) => MatrixPower.residueBits (a : ZMod M)) HE HM

end LeanCanny.Algebra.IntegralMixedFramedBankTermBits

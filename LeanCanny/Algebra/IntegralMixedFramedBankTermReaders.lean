/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankTermPacketValues
/-! # Actual coordinate readers for original-term denominator clearing

The original rational-substitution engine receives only native readers
derived from actual producer leading integers and the joint prefix power
schedule. Numerator variables are reversed into retained-bank order and
zero-extended; every denominator is the literal nonzero common integer Q.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankTermBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey packet)
open scoped Classical

noncomputable def numeratorCode (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (z : List Bool) : List Bool :=
  if active P D H z then IntegralMixedFramedBankCoordinateBits.coefficient P D H (coefficientWidth P D H word) (numeratorPacket P D H z)
  else []

theorem numerator_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    (word : List Bool → List Bool) (hw : word∈FP) : SpaceFunction (numeratorCode P D H word) := by
  have EN := IntegralMixedFramedBankCoordinateBits.coefficient_evaluator P a D H s hs hF hL _ (coefficientWidth_unary P a D H word hw)
  exact (SpaceFunction.branch _ (active_FP P a D H).flag_mem_FP
    (EN.precompose _ (numeratorPacket_FP P a D H)) (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
    (funext fun z => by simp only [numeratorCode,decide_eq_true_eq,Function.comp_apply])

theorem numerator_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (c : List Bool) (i k m : ℕ) (hm : 0<m) :
    numeratorCode P D H word (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m-1)))=
      residueBits (((numerator P D H word c i).coeff k : ℤ) : ZMod m) := by
  have HA : active P D H (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m-1)))↔
      i<(atKey P D H c).count := by
    simp only [active,queriedIndex,IndexedKroneckerReader.context,IndexedKroneckerReader.coordinate,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  unfold numeratorCode
  rw [HA]
  by_cases hi : i<(atKey P D H c).count
  · rw [ite_eq_left hi,numeratorPacket_packet]
    exact coordinate_coefficient_packet P D H word c i k m hi hm
  · rw [ite_eq_right hi,numerator,ite_eq_right hi,Polynomial.coeff_zero,Int.cast_zero]
    exact ArithmeticBits.zero_residueBits _

noncomputable def commonCode (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : List Bool :=
  residueBits ((atKey P D H (PaddedIntegralGeneratorSource.base q)).common : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))
theorem common_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root) : SpaceFunction (commonCode P D H) :=
  (IntegralMixedFramedBankProductBits.common_evaluator P a D H s hs hF hL).congr
    (funext fun q => congrArg (fun z : ℤ => residueBits (z : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))
      (IntegralMixedFramedBankSnapshotBits.common_at P D H q))

noncomputable def denominatorCode (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) : List Bool :=
  if queriedDegree z=0 then commonCode P D H (denominatorPacket z) else []
theorem denominator_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root) : SpaceFunction (denominatorCode P D H) := by
  have ED := common_evaluator P a D H s hs hF hL
  have HG := queriedDegree_binary.eq (BinaryFn.const 0)
  exact (SpaceFunction.branch _ HG.flag_mem_FP (ED.precompose _ denominatorPacket_FP)
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (funext fun z => by simp only [denominatorCode,decide_eq_true_eq,Function.comp_apply])

theorem common_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (m : ℕ) (hm : 0<m) :
    commonCode P D H (packet c (BinaryNatCode.encode (m-1)) 0 0)=residueBits ((atKey P D H c).common : ZMod m) := by
  have HI := congrArg IntegralMixedFramedBankSnapshotBits.Snapshot.common
    (IntegralMixedFramedBankSnapshotBits.packet_snapshot P D H c (BinaryNatCode.encode (m-1)) 0 0)
  have HM : IntegralMixedFramedCompanionQueryBits.callerModulus (packet c (BinaryNatCode.encode (m-1)) 0 0)=m := by
    simp only [IntegralMixedFramedCompanionQueryBits.callerModulus,packet,PaddedIntegralGeneratorSource.modulus,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,Nat.sub_add_cancel hm]
  exact congrArg₂ (fun (a : ℤ) (M : ℕ) => residueBits (a : ZMod M)) HI HM

theorem denominator_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (i k m : ℕ) (hm : 0<m) :
    denominatorCode P D H (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m-1)))=
      residueBits (((denominator P D H c i).coeff k : ℤ) : ZMod m) := by
  have HK : queriedDegree (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m-1)))=k := by
    simp only [queriedDegree,IndexedKroneckerReader.degreeWord,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  unfold denominatorCode denominator
  rw [HK]
  by_cases hk : k=0
  · subst k
    rw [ite_eq_left rfl,Polynomial.coeff_C_zero]
    have HQ : denominatorPacket (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode 0))) (BinaryNatCode.encode (m-1)))=
        packet c (BinaryNatCode.encode (m-1)) 0 0 := by simp only [denominatorPacket,IndexedKroneckerReader.context,pairFst_pair,pairSnd_pair]
    rw [HQ]
    exact common_packet P D H c m hm
  · rw [ite_eq_right hk,Polynomial.coeff_C,ite_eq_right hk,Int.cast_zero]
    exact ArithmeticBits.zero_residueBits _

noncomputable def coordinates (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) : ETR.RationalSubstitutionBits.Coordinates (source word) where
  numerator := numerator P D H word
  denominator := denominator P D H
  numeratorCode := numeratorCode P D H word
  denominatorCode := denominatorCode P D H
  numerator_eq c i _ k m hm := numerator_packet P D H word c i k m hm
  denominator_eq c i _ k m hm := denominator_packet P D H c i k m hm

theorem encoded_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    (word : List Bool → List Bool) (hw : word∈FP) : SpaceFunction (coordinates P D H word).family.value :=
  (coordinates P D H word).evaluator (ETR.RationalSubstitutionBits.Source.ofTerm_polyTime (wordAt_FP word hw))
    (numerator_evaluator P a D H s hs hF hL word hw) (denominator_evaluator P a D H s hs hF hL)

end LeanCanny.Algebra.IntegralMixedFramedBankTermBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankDenominator
public import LeanCanny.Algebra.ModularProductSpace
/-! # Native actual bank common-denominator and cofactor products

The factors are actual chronological producer leading integers derived from
original syntax. Products stream modulo the exact caller modulus. A skipped
retained index gives its cofactor; skipping the prefix length gives common Q.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankProductBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankDenominatorBits (count count_unary integerAt state)
open IntegralMixedFramedCompanionQueryBits (callerModulus)
open scoped Classical BigOperators

noncomputable def integer (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (skip : List Bool → ℕ) (q : List Bool) : ℤ :=
  ∏ i ∈ Finset.range (count P D H q), if i=skip q then 1 else integerAt P D H q i
noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (skip : List Bool → ℕ) (q : List Bool) : List Bool := residueBits (integer P D H skip q : ZMod (callerModulus q))

def factorPacket (z : List Bool) :=
  pair (pair (PaddedIntegralGeneratorSource.base (pairFst z)) (PaddedIntegralGeneratorSource.modulus (pairFst z)))
    (pair (pairSnd z) [])
theorem factorPacket_FP : factorPacket∈FP := by
  have HB : (fun z => PaddedIntegralGeneratorSource.base (pairFst z))∈FP :=
    mem_FP_comp (f := pairFst) (g := PaddedIntegralGeneratorSource.base) pairFst_mem_FP PaddedIntegralGeneratorSource.base_FP
  have HM : (fun z => PaddedIntegralGeneratorSource.modulus (pairFst z))∈FP :=
    mem_FP_comp (f := pairFst) (g := PaddedIntegralGeneratorSource.modulus) pairFst_mem_FP PaddedIntegralGeneratorSource.modulus_FP
  exact mem_FP_pair (mem_FP_pair HB HM) (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP []))

noncomputable def factor (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (skip : List Bool → ℕ) (z : List Bool) :=
  if Nat.fromBitsLE (pairSnd z)=skip (pairFst z) then IntegralMixedFramedLeadingBits.defaultValue (pairFst z)
  else IntegralMixedFramedBankDenominatorBits.value P D H (factorPacket z)

theorem factor_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root) (skip : List Bool → ℕ) (hk : BinaryFn skip) :
    SpaceFunction (factor P D H skip) := by
  have ED := IntegralMixedFramedBankDenominatorBits.evaluator P a D H s hs hF hL
  have EO := (SpaceFunction.ofFP _ IntegralMixedFramedLeadingBits.defaultValue_FP).precompose pairFst pairFst_mem_FP
  have HG := (BinaryFn.fromBits pairSnd_mem_FP).eq (hk.comp pairFst_mem_FP)
  exact (SpaceFunction.branch _ HG.flag_mem_FP EO (ED.precompose factorPacket factorPacket_FP)).congr
    (funext fun z => by simp only [factor,decide_eq_true_eq,Function.comp_apply])

private noncomputable def integerAtKey (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : ℕ) : ℤ :=
  if hi : i<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth key then
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).bank.denominator ⟨i,hi⟩ else 0

theorem factor_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (skip : List Bool → ℕ) (q : List Bool) (i : ℕ) :
    factor P D H skip (pair q (BinaryNatCode.encode i))=
      residueBits ((if i=skip q then 1 else integerAt P D H q i : ℤ) : ZMod (callerModulus q)) := by
  simp only [factor,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  by_cases hi : i=skip q
  · rw [ite_eq_left hi,ite_eq_left hi]
    have HH := ArithmeticBits.one_residueBits (callerModulus q)
    have HI : ((1 : ℤ) : ZMod (callerModulus q))=1 := Int.cast_one
    rw [HI]
    simpa only [IntegralMixedFramedLeadingBits.defaultValue,BinaryNat.succ_eq_bits,callerModulus,BinaryNatCode.encode] using HH
  · rw [ite_eq_right hi,ite_eq_right hi]
    have HI : integerAt P D H (factorPacket (pair q (BinaryNatCode.encode i)))
        (IntegralMixedFramedBankDenominatorBits.index (factorPacket (pair q (BinaryNatCode.encode i))))=integerAt P D H q i := by
      change integerAtKey P D H (PaddedIntegralGeneratorSource.base (factorPacket (pair q (BinaryNatCode.encode i))))
        (IntegralMixedFramedBankDenominatorBits.index (factorPacket (pair q (BinaryNatCode.encode i))))=
        integerAtKey P D H (PaddedIntegralGeneratorSource.base q) i
      simp only [factorPacket,PaddedIntegralGeneratorSource.base,IntegralMixedFramedBankDenominatorBits.index,
        PaddedIntegralGeneratorSource.row,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    have HM : callerModulus (factorPacket (pair q (BinaryNatCode.encode i)))=callerModulus q := by
      simp only [factorPacket,callerModulus,PaddedIntegralGeneratorSource.modulus,pairFst_pair,pairSnd_pair]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m)) HI HM

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root) (skip : List Bool → ℕ) (hk : BinaryFn skip) :
    SpaceFunction (value P D H skip) := by
  have EC := (BinaryFn.ofUnary (count_unary P a D H)).bits_mem_FP
  have EM := IntegralMixedFramedCompanionQueryBits.callerModulus_binary.bits_mem_FP
  have EE := ModularProduct.evaluatorWithModulus (factor_evaluator P a D H s hs hF hL skip hk)
    (fun q => BinaryNatCode.encode (count P D H q)) (fun q => BinaryNatCode.encode (callerModulus q)) EC EM
    callerModulus (funext fun q => Nat.fromBitsLE_bits _)
    (fun q i => ((if i=skip q then 1 else integerAt P D H q i : ℤ) : ZMod (callerModulus q)))
    (fun q => by unfold callerModulus; omega) (fun q i _ => factor_packet P D H skip q i)
  exact EE.congr (funext fun q => by
    simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits,value,integer,Int.cast_prod])

theorem integer_fin (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (skip : List Bool → ℕ) (q : List Bool) :
    integer P D H skip q=∏ i : Fin (count P D H q), if i.val=skip q then 1 else (state P D H q).bank.denominator i := by
  unfold integer
  rw [← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  unfold integerAt
  rw [dite_eq_left i.isLt]
  rfl

theorem common_integer (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    integer P D H (count P D H) q=IntegralMixedHistory.commonDenominator (state P D H q) := by
  rw [integer_fin]
  unfold IntegralMixedHistory.commonDenominator CommonIntegerDenominator.denominator
  apply Finset.prod_congr rfl
  intro i _
  rw [ite_eq_right (Nat.ne_of_lt i.isLt)]

theorem common_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root) :
    SpaceFunction (fun q => residueBits (IntegralMixedHistory.commonDenominator (state P D H q) : ZMod (callerModulus q))) :=
  (evaluator P a D H s hs hF hL (count P D H) (BinaryFn.ofUnary (count_unary P a D H))).congr
    (funext fun q => by unfold value; rw [common_integer])

end LeanCanny.Algebra.IntegralMixedFramedBankProductBits

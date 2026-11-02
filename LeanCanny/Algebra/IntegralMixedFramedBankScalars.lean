/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQBankProducts
public import LeanCanny.Algebra.IntegralMixedFramedBankTermBounds
public import LeanCanny.Algebra.IntegerPolynomialRationalPointSpace

/-! # Actual retained-bank scalars for implicit univariate tests

The numerator is the actual retained cofactor and the denominator is the
common integer of the same saved bank. Both native residue readers preserve
the entire caller modulus. No integer term serialization is required.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankScalars
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralMixedFramedBankSnapshotBits (atKey packet)
open RationalSubstitution.IntegerBits (context mValue context_mem_FP)
open scoped Classical

noncomputable def scalars (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (index : List Bool→ℕ) : IntegerPolynomialRationalPointSource.Scalars where
  numerator q:=(atKey P D H (key q)).cofactor (index q)
  denominator q:=(atKey P D H (key q)).common
  mass q:=IntegralMixedFramedBankTermBits.coordinateMass P D H L F C (key q)
  numerator_bound q:=IntegralMixedFramedBankTermBits.snapshot_cofactor_bound _ _
    (fun i=>(IntegralMixedFramedStepHeight.family_bank_bounds P D H L F C hs (key q)).denominator i) _
  denominator_bound q:=IntegralMixedFramedBankTermBits.snapshot_common_bound _ _
    (fun i=>(IntegralMixedFramedStepHeight.family_bank_bounds P D H L F C hs (key q)).denominator i)

def query (key : List Bool→List Bool) (index : List Bool→ℕ) (q : List Bool) : List Bool :=
  packet (key (context q)) (pairSnd q) (index (context q)) 0

theorem query_FP {key : List Bool→List Bool} {index : List Bool→ℕ} (hkey : key∈FP) (hi : BinaryFn index) :
    query key index∈FP := by
  have HI : BinaryFn (fun q=>index (context q)):=hi.comp context_mem_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_comp context_mem_FP hkey) pairSnd_mem_FP)
    (mem_FP_pair HI.bits_mem_FP (constFn_mem_FP (BinaryNatCode.encode 0)))

theorem query_modulus (key : List Bool→List Bool) (index : List Bool→ℕ) (q : List Bool) :
    IntegralMixedFramedCompanionQueryBits.callerModulus (query key index q)=mValue q := by
  simp only [query,packet,IntegralMixedFramedCompanionQueryBits.callerModulus,
    PaddedIntegralGeneratorSource.modulus,pairFst_pair,pairSnd_pair]

theorem access (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew c)
    {L F C : List Bool→ℕ} (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    {key : List Bool→List Bool} {index : List Bool→ℕ} (hkey : key∈FP) (hi : BinaryFn index) :
    IntegerPolynomialRationalPointSource.Access (scalars P D H L F C hs key index) where
  mass:=(IntegralMixedFramedBankTermBits.coordinateMass_binary P a D H hL hF hC).comp hkey
  numerator:=by
    have E:=IntegralMixedFramedCurrentQBankProductBits.evaluator P a D H Hnew c hb _
      IntegralMixedFramedBankDenominatorBits.index_binary
    refine (E.precompose (query key index) (query_FP hkey hi)).congr (funext fun q=>?_)
    exact congrArg₂ (fun (z : ℤ) (M : ℕ)=>residueBits (z : ZMod M))
      (IntegralMixedFramedBankSnapshotBits.cofactor_packet P D H _ _ _ _) (query_modulus key index q)
  denominator:=by
    have E:=IntegralMixedFramedCurrentQBankProductBits.common_evaluator P a D H Hnew c hb
    refine (E.precompose (query key index) (query_FP hkey hi)).congr (funext fun q=>?_)
    have HI : IntegralMixedHistory.commonDenominator
        (IntegralMixedFramedBankDenominatorBits.state P D H (query key index q))=
          (atKey P D H (key (context q))).common := by
      rw [IntegralMixedFramedBankSnapshotBits.common_at]
      exact congrArg (fun k=>(atKey P D H k).common) (IntegralMixedFramedBankSnapshotBits.packet_base _ _ _ _)
    exact congrArg₂ (fun (z : ℤ) (M : ℕ)=>residueBits (z : ZMod M)) HI (query_modulus key index q)

end LeanCanny.Algebra.IntegralMixedFramedBankScalars

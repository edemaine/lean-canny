/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankScalars

/-! # Original syntax supplies actual retained-bank scalar readers

The existing original controller performs its own normalization planning and
caller-modulus pullback. This discharges the bank scalar costs for an original
candidate without supplying a separately planned controller.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankScalarsOriginal
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open IntegralMixedFramedBankScalars (scalars query query_FP query_modulus)
open RationalSubstitution.IntegerBits (context mValue)
open scoped Classical

theorem access (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    {L F C : List Bool→ℕ} (hLB : BinaryFn L) (hFB : BinaryFn F) (hCB : BinaryFn C)
    (hB : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    {key : List Bool→List Bool} {index : List Bool→ℕ} (hk : key∈FP) (hi : BinaryFn index) :
    IntegerPolynomialRationalPointSource.Access (scalars P D H L F C hB key index) where
  mass:=(IntegralMixedFramedBankTermBits.coordinateMass_binary P a D H hLB hFB hCB).comp hk
  numerator:=by
    have E:=IntegralMixedFramedBankProductBits.evaluator P a D H s hs hF hL _
      IntegralMixedFramedBankDenominatorBits.index_binary
    refine (E.precompose (query key index) (query_FP hk hi)).congr (funext fun q=>?_)
    exact congrArg₂ (fun (z : ℤ) (M : ℕ)=>residueBits (z : ZMod M))
      (IntegralMixedFramedBankSnapshotBits.cofactor_packet P D H _ _ _ _) (query_modulus key index q)
  denominator:=by
    have E:=IntegralMixedFramedBankProductBits.common_evaluator P a D H s hs hF hL
    refine (E.precompose (query key index) (query_FP hk hi)).congr (funext fun q=>?_)
    have HI : IntegralMixedHistory.commonDenominator
        (IntegralMixedFramedBankDenominatorBits.state P D H (query key index q))=
          (atKey P D H (key (context q))).common := by
      rw [IntegralMixedFramedBankSnapshotBits.common_at]
      exact congrArg (fun k=>(atKey P D H k).common) (IntegralMixedFramedBankSnapshotBits.packet_base _ _ _ _)
    exact congrArg₂ (fun (z : ℤ) (M : ℕ)=>residueBits (z : ZMod M)) HI (query_modulus key index q)

end LeanCanny.Algebra.IntegralMixedFramedBankScalarsOriginal

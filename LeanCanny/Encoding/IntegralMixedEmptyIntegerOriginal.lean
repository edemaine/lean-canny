/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedEmptyUnitLookup
public import LeanCanny.Algebra.IntegralMixedFramedIntegerSyntax
/-! # Constant X supplies every original integer leaf of the empty route

Actual records are noninteger. The only integer instruction is the padded
default X, and the total original integer family also pads noninteger
contexts by X. Its native degree and coefficient leaves follow from the
constant original term word var0, without any bank-source assumptions.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedEmptyUnitPlan
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCanonicalUnitSourceBits (Originals source)
open scoped Classical

private noncomputable def integerPolynomial {n B : ℕ} (I : Instruction n B) : Polynomial ℤ :=
  match I.command with
  | .integer p _ _ => p
  | _ => Polynomial.X

private theorem polynomial_instruction (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (key : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial P D key=
      integerPolynomial (IntegralMixedFramedHistoryFamilyBits.instruction P D key) := by
  unfold IntegralMixedFramedIntegerBits.polynomial integerPolynomial
  cases (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;> rfl

theorem polynomial_X (P : Parameters) (O : Originals P)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hroom : ∀ root, count root+2≤P.cap root+1) (key : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial P (plan P O hn hcap hroom) key=Polynomial.X := by
  rw [polynomial_instruction]
  by_cases hl : inRecords P key
  · rw [instruction_record P O hn hcap hroom key hl]
    unfold step integerPolynomial IntegralMixedCanonicalUnitRuleBits.command
    dsimp only
    split_ifs <;> rfl
  · rw [instruction_default P O hn hcap hroom key hl]
    rfl

def integerWord (_ : List Bool) : List Bool := (ETR.Term.var 0).toData.toBits

theorem integerWord_FP : integerWord∈FP := constFn_mem_FP _

theorem integerWord_polynomial (P : Parameters) (O : Originals P)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hroom : ∀ root, count root+2≤P.cap root+1) (key : List Bool) :
    ETR.IntegerUnivariateTermSource.polynomial integerWord key=
      IntegralMixedFramedIntegerBits.polynomial P (plan P O hn hcap hroom) key := by
  rw [polynomial_X P O hn hcap hroom key]
  unfold ETR.IntegerUnivariateTermSource.polynomial integerWord
  rw [ETR.TermView.term_toBits]
  rfl

theorem integerOriginal (P : Parameters) (a : Access P) (O : Originals P)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hroom : ∀ root, count root+2≤P.cap root+1) :
    IntegralMixedIntegerFamilyBits.Original P (IntegralMixedFramedIntegerBits.polynomial P (plan P O hn hcap hroom)) :=
  IntegralMixedFramedIntegerSyntaxBits.original P a _ integerWord integerWord_FP
    (integerWord_polynomial P O hn hcap hroom)

end LeanCanny.Encoding.IntegralMixedEmptyUnitPlan

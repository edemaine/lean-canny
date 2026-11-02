/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedEmptyUnitLookup
public import LeanCanny.Encoding.IntegralMixedUnitRecordSemantics
/-! # Total literal rules for the empty-prelude source-framed family -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedEmptyUnitPlan
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCanonicalUnitSourceBits (Originals source)
open scoped Classical

variable (P : Parameters) (O : Originals P)
  (hn : ∀ root, 0<P.ambient root)
  (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (hroom : ∀ root, count root+2≤P.cap root+1)
  (hSW : ∀ root, (P.degree root).size≤P.sourceWidth root)

noncomputable def data : IntegralMixedFramedHistoryFamilyBits.Data P (plan P O hn hcap hroom) where
  degree_eq key := by rw [instruction_source P O hn hcap hroom]; rfl
  sourceWidth key := by rw [instruction_source P O hn hcap hroom]; exact hSW (pairFst key)
  fallback key := IntegralMixedCanonicalUnitRuleBits.selection
    (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O hn hcap hroom) key).source
    (hn (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (selectedCode P key)

private theorem critical_nil : IntegralMixedUnitRecordCode.critical []=false := rfl

private noncomputable def virtualOf {n B : ℕ} (I : Instruction n B)
    (fallback : IntegralMixedCriticalSweep.Rule n) : IntegralMixedCriticalSweep.Rule n :=
  match I.command with
  | .cut r _ _ _ _ => r
  | _ => fallback

private noncomputable def physicalOf {n B : ℕ} (I : Instruction n B) : CriticalRule n :=
  match I.command with
  | .critical r => r
  | _ => IntegralMixedFullPhysicalBits.defaultRule n

theorem virtual_rule (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family P (plan P O hn hcap hroom) (data P O hn hcap hroom hSW)).rule key=
      IntegralMixedCanonicalUnitRuleBits.virtual (P.ambient (pairFst key)) (hn (pairFst key))
        (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (selectedCode P key) := by
  change (IntegralMixedFramedHistoryFamilyBits.selection P _ _ key).rule=_
  have HE : (IntegralMixedFramedHistoryFamilyBits.selection P (plan P O hn hcap hroom)
      (data P O hn hcap hroom hSW) key).rule=
      virtualOf (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O hn hcap hroom) key)
        ((data P O hn hcap hroom hSW).fallback key).rule := by
    unfold IntegralMixedFramedHistoryFamilyBits.selection virtualOf
    cases (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O hn hcap hroom) key).command <;> rfl
  refine HE.trans ?_
  change virtualOf (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O hn hcap hroom) key)
    (IntegralMixedCanonicalUnitRuleBits.virtual _ (hn _) _ (selectedCode P key))=_
  by_cases hl : inRecords P key
  · rw [instruction_record P O hn hcap hroom key hl]
    simp only [step,selectedCode,ite_eq_left hl]
    unfold virtualOf IntegralMixedCanonicalUnitRuleBits.command
    dsimp only
    split_ifs <;> rfl
  · rw [selectedCode,ite_eq_right hl,instruction_default P O hn hcap hroom key hl]
    rfl

theorem physical_rule (key : List Bool) :
    IntegralMixedFramedPhysicalBits.rule P (plan P O hn hcap hroom) key=
      if IntegralMixedUnitRecordCode.critical (selectedCode P key) then
        IntegralMixedCanonicalUnitRuleBits.physical (P.ambient (pairFst key))
          (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (selectedCode P key)
      else IntegralMixedFullPhysicalBits.defaultRule (P.ambient (pairFst key)) := by
  have HE : IntegralMixedFramedPhysicalBits.rule P (plan P O hn hcap hroom) key=
      physicalOf (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O hn hcap hroom) key) := by
    unfold IntegralMixedFramedPhysicalBits.rule physicalOf
    cases (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O hn hcap hroom) key).command <;> rfl
  refine HE.trans ?_
  by_cases hl : inRecords P key
  · rw [instruction_record P O hn hcap hroom key hl]
    simp only [step,selectedCode,ite_eq_left hl]
    unfold physicalOf IntegralMixedCanonicalUnitRuleBits.command
    dsimp only
    split_ifs <;> rfl
  · simp only [selectedCode,ite_eq_right hl,critical_nil,Bool.false_eq_true,ite_false]
    rw [instruction_default P O hn hcap hroom key hl]
    rfl

end LeanCanny.Encoding.IntegralMixedEmptyUnitPlan

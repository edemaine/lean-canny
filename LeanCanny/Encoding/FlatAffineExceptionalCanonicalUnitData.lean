/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitLookup
public import LeanCanny.Encoding.IntegralMixedUnitRecordSemantics
/-! # A total canonical family has the same literal unit rules as its records -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitPlan
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCanonicalUnitSourceBits (Originals source)
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (O : Originals P) (F : Inputs)
  (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
  (hn : ∀ root, 0<P.ambient root)
  (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root) ≤ 2^P.width root)
  (hW : ∀ root, FlatAffineExceptionalBankSource.width F (input root) ≤ P.width root)
  (hroom : ∀ root, count root+seedCount F root+2 ≤ P.cap root+1)
  (hSW : ∀ root, (P.degree root).size ≤ P.sourceWidth root)

noncomputable def data : IntegralMixedFramedHistoryFamilyBits.Data P (plan P O F C h hn hcap hW hroom) where
  degree_eq key := by rw [instruction_source P O F C h hn hcap hW hroom]; rfl
  sourceWidth key := by rw [instruction_source P O F C h hn hcap hW hroom]; exact hSW (pairFst key)
  fallback key := IntegralMixedCanonicalUnitRuleBits.selection
    (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O F C h hn hcap hW hroom) key).source
    (hn (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (selectedCode P F key)

private theorem critical_nil : IntegralMixedUnitRecordCode.critical [] = false := rfl

private noncomputable def virtualOf {n B : ℕ} (I : Instruction n B)
    (fallback : IntegralMixedCriticalSweep.Rule n) : IntegralMixedCriticalSweep.Rule n :=
  match I.command with
  | .cut r _ _ _ _ => r
  | _ => fallback

private noncomputable def physicalOf {n B : ℕ} (I : Instruction n B) : CriticalRule n :=
  match I.command with
  | .critical r => r
  | _ => IntegralMixedFullPhysicalBits.defaultRule n

private theorem selection_rule {n B : ℕ} (I : Instruction n B)
    (fallback : IntegralMixedFullHistoryFamilyBits.Selection I.source) :
    (match I.command with
    | .cut r k d ha _ => (⟨r,k,d,ha⟩ : IntegralMixedFullHistoryFamilyBits.Selection I.source)
    | _ => fallback).rule = virtualOf I fallback.rule := by
  unfold virtualOf
  cases I.command <;> rfl

theorem virtual_rule (key : List Bool) :
    ((IntegralMixedFramedHistoryFamilyBits.family P (plan P O F C h hn hcap hW hroom) (data P O F C h hn hcap hW hroom hSW)).rule key) =
      IntegralMixedCanonicalUnitRuleBits.virtual (P.ambient (pairFst key)) (hn (pairFst key))
        (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (selectedCode P F key) := by
  change (IntegralMixedFramedHistoryFamilyBits.selection P _ _ key).rule = _
  have HE : (IntegralMixedFramedHistoryFamilyBits.selection P (plan P O F C h hn hcap hW hroom) (data P O F C h hn hcap hW hroom hSW) key).rule =
      virtualOf (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O F C h hn hcap hW hroom) key)
        ((data P O F C h hn hcap hW hroom hSW).fallback key).rule := by
    unfold IntegralMixedFramedHistoryFamilyBits.selection virtualOf
    cases (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O F C h hn hcap hW hroom) key).command <;> rfl
  refine HE.trans ?_
  change virtualOf (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O F C h hn hcap hW hroom) key)
    (IntegralMixedCanonicalUnitRuleBits.virtual _ (hn _) _ (selectedCode P F key)) = _
  by_cases hl : inLater P F key
  · rw [instruction_later P O F C h hn hcap hW hroom key hl]
    simp only [step, Nat.add_sub_of_le hl.1, selectedCode, ite_eq_left hl]
    unfold virtualOf IntegralMixedCanonicalUnitRuleBits.command
    dsimp only
    split_ifs <;> rfl
  · rw [selectedCode, ite_eq_right hl]
    by_cases hb : IntegralMixedFramedHistoryFamilyBits.prefixLength P key<seedCount F (pairFst key)
    · rw [instruction_prefix P O F C h hn hcap hW hroom key hb]
      rfl
    · rw [instruction_default P O F C h hn hcap hW hroom key (Nat.le_of_not_gt hb) hl]
      rfl

theorem physical_rule (key : List Bool) :
    (IntegralMixedFramedPhysicalBits.rule P (plan P O F C h hn hcap hW hroom) key) =
      if IntegralMixedUnitRecordCode.critical (selectedCode P F key) then
        IntegralMixedCanonicalUnitRuleBits.physical (P.ambient (pairFst key))
          (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (selectedCode P F key)
      else IntegralMixedFullPhysicalBits.defaultRule (P.ambient (pairFst key)) := by
  have HE : IntegralMixedFramedPhysicalBits.rule P (plan P O F C h hn hcap hW hroom) key =
      physicalOf (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O F C h hn hcap hW hroom) key) := by
    unfold IntegralMixedFramedPhysicalBits.rule physicalOf
    cases (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O F C h hn hcap hW hroom) key).command <;> rfl
  refine HE.trans ?_
  by_cases hl : inLater P F key
  · rw [instruction_later P O F C h hn hcap hW hroom key hl]
    simp only [step, Nat.add_sub_of_le hl.1]
    rw [selectedCode, ite_eq_left hl]
    unfold physicalOf IntegralMixedCanonicalUnitRuleBits.command
    dsimp only
    split_ifs <;> rfl
  · simp only [selectedCode, ite_eq_right hl, critical_nil, Bool.false_eq_true, ite_false]
    by_cases hb : IntegralMixedFramedHistoryFamilyBits.prefixLength P key<seedCount F (pairFst key)
    · rw [instruction_prefix P O F C h hn hcap hW hroom key hb]
      rfl
    · rw [instruction_default P O F C h hn hcap hW hroom key (Nat.le_of_not_gt hb) hl]
      rfl
end LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitPlan

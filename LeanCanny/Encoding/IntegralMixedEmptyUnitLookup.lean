/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedEmptyUnitPlan
/-! # Actual chronological sources of the empty-prelude canonical plan -/
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

theorem instruction_record (key : List Bool) (hl : inRecords P key) :
    IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O hn hcap hroom) key=
      step P O hn hcap (pairFst key) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) := by
  change IntegralMixedFramedHistoryFamilyBits.prefixLength P key<count (pairFst key) at hl
  unfold IntegralMixedFramedHistoryFamilyBits.instruction
  change (chronological (rules P O hn hcap (pairFst key))
    (IntegralMixedFramedHistoryFamilyBits.prefixLength P key)).getD _ = _
  rw [rules_chronological,dite_eq_left hl]
  rfl

theorem instruction_default (key : List Bool) (hl : ¬inRecords P key) :
    IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O hn hcap hroom) key=
      IntegralMixedFramedHistoryFamilyBits.defaultInstruction P (plan P O hn hcap hroom) (pairFst key) := by
  change ¬IntegralMixedFramedHistoryFamilyBits.prefixLength P key<count (pairFst key) at hl
  unfold IntegralMixedFramedHistoryFamilyBits.instruction
  change (chronological (rules P O hn hcap (pairFst key))
    (IntegralMixedFramedHistoryFamilyBits.prefixLength P key)).getD _ = _
  rw [rules_chronological,dite_eq_right hl]
  rfl

noncomputable def sourceIndex (key : List Bool) :=
  if inRecords P key then IntegralMixedFramedHistoryFamilyBits.prefixLength P key else 0

theorem sourceIndex_unary (a : Access P) : UnaryFn (sourceIndex P) :=
  UnaryFn.ite (inRecords_FP P a) (IntegralMixedFullHistoryFamilyBits.prefix_unary P a) (UnaryFn.const 0)

theorem instruction_source (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O hn hcap hroom) key).source=
      source P O (pairFst key) (sourceIndex P key) := by
  by_cases hl : inRecords P key
  · rw [instruction_record P O hn hcap hroom key hl,sourceIndex,ite_eq_left hl]
    rfl
  · rw [instruction_default P O hn hcap hroom key hl,sourceIndex,ite_eq_right hl]
    rfl

theorem rules_noninteger (root : List Bool) (c : Instruction (P.ambient root) (P.width root))
    (hc : c∈rules P O hn hcap root) : c.command.context≠0 := by
  change c∈(((List.range (count root)).map (step P O hn hcap root)).reverse) at hc
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
  change (IntegralMixedCanonicalUnitRuleBits.command (source P O root i) (hn root) i (code root i) (hcap root)).context≠0
  unfold IntegralMixedCanonicalUnitRuleBits.command
  split_ifs
  · exact Nat.one_ne_zero
  · exact (by decide : (2:ℕ)≠0)

end LeanCanny.Encoding.IntegralMixedEmptyUnitPlan

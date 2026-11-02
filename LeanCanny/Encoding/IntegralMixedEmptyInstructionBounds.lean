/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCanonicalUnitRules
public import LeanCanny.Algebra.IntegralMixedFramedPrefixHeight
/-! # Unit original records have fixed command size and unit scalar cells -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedEmptyInstructionBounds
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedStepHeight
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem expression_nodes (code : List Bool) (b i : ℕ) :
    (IntegralMixedUnitRowCode.expression code b i).nodes=1 := by
  unfold IntegralMixedUnitRowCode.expression
  split_ifs <;> rfl

theorem expression_coefficients (code : List Bool) (b i C : ℕ) :
    (IntegralMixedUnitRowCode.expression code b i).CoefficientsBound C := by
  unfold IntegralMixedUnitRowCode.expression
  split_ifs
  · trivial
  · exact Nat.zero_le C

theorem command_bounds {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (b : ℕ) (code : List Bool)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B) (C : ℕ) (hC : 1≤C) :
    IntegralMixedFullScriptHeight.CommandBounds C 1 (IntegralMixedCanonicalUnitRuleBits.command S hn b code hcap) := by
  unfold IntegralMixedCanonicalUnitRuleBits.command
  split_ifs
  · refine ⟨?_,?_,?_⟩
    · intro i
      exact (expression_nodes _ _ _).le
    · intro i
      exact expression_coefficients _ _ _ C
    · intro i
      simpa only [IntegralMixedCanonicalUnitRuleBits.physical,Int.natAbs_one,Nat.size_one] using hC
  · refine ⟨?_,?_,?_,?_⟩
    · intro i
      exact (expression_nodes _ _ _).le
    · intro i
      exact expression_coefficients _ _ _ C
    · intro i
      simpa only [IntegralMixedCanonicalUnitRuleBits.virtual,Int.natAbs_one,Nat.size_one] using hC
    · simpa only [IntegralMixedCanonicalUnitRuleBits.virtual,Int.natAbs_one,Nat.size_one] using hC

/-- A chronological range is charged at its actual birth before reversal. -/
theorem reverse_range_bounds {n B : ℕ} (S W D L F C : ℕ) (step : ℕ → Instruction n B) (N : ℕ)
    (h : ∀ b, b<N → InstructionBounds (height n S B W D L F C b) F W D L (step b)) :
    ScriptBounds S W D L F C (((List.range N).map step).reverse) := by
  induction N with
  | zero => trivial
  | succ N ih =>
    rw [List.range_succ,List.map_append,List.map_cons,List.map_nil,List.reverse_append]
    change ScriptBounds S W D L F C (((List.range N).map step).reverse) ∧
      InstructionBounds (height n S B W D L F C (((List.range N).map step).reverse).length) F W D L (step N)
    refine ⟨ih (fun b hb => h b (by omega)),?_⟩
    simpa only [List.length_reverse,List.length_map,List.length_range] using h N (Nat.lt_succ_self N)
end LeanCanny.Encoding.IntegralMixedEmptyInstructionBounds

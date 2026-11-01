/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedDenominatorPrefix
/-! # Actual creating polynomial leading scalars from the charged forward pass -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedDenominatorScriptBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralMixedHistory IntegralMixedHistoryScript IntegralMixedDenominatorBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def creatingLeading (F : Family) (birth : List Bool → ℕ) (c : List Bool) : ℤ :=
  if birth c < count F c then (descriptorAt F c (birth c)).value (IntegralDenominatorPass.integers (program F) c (birth c)) else 0

theorem creating_leading_evaluator (F : Family) (a : Access F) (birth : List Bool → ℕ) (hb : UnaryFn birth) :
    SpaceFunction (fun c => residueBits (creatingLeading F birth c : ZMod (F.modulus c))) := by
  have E := prefix_denominator_evaluator F a (fun c => birth c + 1) (hb.add (UnaryFn.const 1)) (fun _ => 0) (BinaryFn.const 0)
  have HC := (BinaryFn.ofUnary hb).lt (BinaryFn.ofUnary a.count)
  have Z : SpaceFunction (fun c => residueBits (0 : ZMod (F.modulus c))) :=
    (SpaceFunction.ofFP _ (constFn_mem_FP [])).congr (funext fun _ => by simp [residueBits, BinaryNatCode.encode])
  refine (SpaceFunction.branch (fun c => decide (birth c < count F c)) HC.flag_mem_FP E Z).congr (funext fun c => ?_)
  by_cases h : birth c < count F c
  · simp only [h, decide_true, ite_true, creatingLeading]
    unfold prefixCount
    rw [min_eq_left (Nat.succ_le_of_lt h), IntegralDenominatorPass.integers]
    change residueBits (IntegralDenominatorPass.integerNext (program F) c (birth c)
      (IntegralDenominatorPass.integers (program F) c (birth c)) : ZMod (F.modulus c)) = _
    rw [next_descriptor]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, creatingLeading, Int.cast_zero]

theorem creatingLeading_actual {S m : ℕ} (F : Family) (c : List Bool) {ι : Type}
    (x : State (F.spatial c) S (F.width c) m ι) (hm : m ≤ S) (cmd : Command (F.ambient c) (F.width c))
    (hv : m < count F c) (hc : commandAt F c m = some cmd)
    (hx : bankList x = IntegralDenominatorPass.integers (program F) c m) :
    creatingLeading F (fun _ => m) c = IntegralMixedHistoryScript.leading x hm cmd := by
  unfold creatingLeading
  rw [ite_eq_left hv]
  unfold descriptorAt
  rw [hc, min_eq_left hv.le, instruction_value _ _ m _ (IntegralDenominatorPass.integers_length _ _ _), leading_eq, hx]
end LeanCanny.Algebra.IntegralMixedDenominatorScriptBits

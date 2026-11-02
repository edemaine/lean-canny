/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryStepHeight
public import LeanCanny.Algebra.IntegralMixedFramedRunHeight
/-! # Native binary access to the derived canonical sampling-height recurrence

The recursion performs the proved actual bank charge. Its closed form has a
native binary evaluator from original dimension, degree, width, horizon and
seed controls; the level integer is never serialized.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedCausalLevelSchedule

def scheduledHeight (n S B D C j : ℕ) : ℕ := nextHeight n S B D 1^j*(C+1)
def recursiveHeight (n S B D C : ℕ) : ℕ → ℕ
  | 0 => C+1
  | j+1 => nextHeight n S B D (recursiveHeight n S B D C j)

theorem nextHeight_scheduled (n S B D C j : ℕ) :
    nextHeight n S B D (scheduledHeight n S B D C j)=scheduledHeight n S B D C (j+1) := by
  simp only [scheduledHeight,nextHeight,Nat.mul_one,pow_succ',Nat.mul_assoc]

theorem recursiveHeight_eq_scheduled (n S B D C j : ℕ) :
    recursiveHeight n S B D C j=scheduledHeight n S B D C j := by
  induction j with
  | zero => simp only [recursiveHeight,scheduledHeight,pow_zero,one_mul]
  | succ j ih =>
    change nextHeight n S B D (recursiveHeight n S B D C j)=_
    rw [ih]
    exact nextHeight_scheduled n S B D C j

theorem seed_le_scheduledHeight (n S B D C j : ℕ) : C+1≤scheduledHeight n S B D C j := by
  have HP := Nat.one_le_pow j (nextHeight n S B D 1) (nextHeight_pos n S B D 1 (Nat.le_refl _))
  simpa only [scheduledHeight,one_mul] using Nat.mul_le_mul_right (C+1) HP

theorem recursiveHeight_positive (n S B D C j : ℕ) : 1≤recursiveHeight n S B D C j := by
  rw [recursiveHeight_eq_scheduled]
  exact (Nat.succ_pos C).trans_le (seed_le_scheduledHeight n S B D C j)

theorem seed_le_recursiveHeight (n S B D C j : ℕ) : C+1≤recursiveHeight n S B D C j := by
  rw [recursiveHeight_eq_scheduled]
  exact seed_le_scheduledHeight n S B D C j

theorem sourceFactor_binary {n S B D : List Bool → ℕ}
    (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B) (hD : BinaryFn D) :
    BinaryFn (fun q => sourceFactor (n q) (S q) (B q) (D q)) := by
  simpa only [sourceFactor] using cfactor_binary (hn.add (UnaryFn.const 1)) hD
    (IntegralMixedFullScriptHeight.rank_binary hS hB)

theorem nextHeight_binary {n S B D G : List Bool → ℕ}
    (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B) (hD : BinaryFn D) (hG : BinaryFn G) :
    BinaryFn (fun q => nextHeight (n q) (S q) (B q) (D q) (G q)) := by
  have HM : BinaryFn (fun q => FixedLeadingTiltedSource.degree (D q)) :=
    ((BinaryFn.const 4).mul hD).add (BinaryFn.const 2)
  have HW : UnaryFn (fun q => (FixedLeadingTiltedSource.degree (D q)).size) :=
    (UnaryFn.length HM.bits_mem_FP).of_eq (fun q => BinaryNatCode.length_encode (FixedLeadingTiltedSource.degree (D q)))
  have HF := (sourceFactor_binary hn hS hB hD).add (BinaryFn.const 2)
  exact (IntegralMixedFramedStepHeight.growth_binary (hn.add (UnaryFn.const 2)) hS hB HW HM (BinaryFn.const 1) HF).mul hG

theorem scheduledHeight_binary {n S B D C j : List Bool → ℕ}
    (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B) (hD : BinaryFn D) (hC : BinaryFn C) (hj : UnaryFn j) :
    BinaryFn (fun q => scheduledHeight (n q) (S q) (B q) (D q) (C q) (j q)) :=
  ((nextHeight_binary hn hS hB hD (BinaryFn.const 1)).powUnary hj).mul (hC.add (BinaryFn.const 1))

theorem recursiveHeight_binary {n S B D C j : List Bool → ℕ}
    (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B) (hD : BinaryFn D) (hC : BinaryFn C) (hj : UnaryFn j) :
    BinaryFn (fun q => recursiveHeight (n q) (S q) (B q) (D q) (C q) (j q)) :=
  (scheduledHeight_binary hn hS hB hD hC hj).of_eq (fun q => (recursiveHeight_eq_scheduled (n q) (S q) (B q) (D q) (C q) (j q)).symm)

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory

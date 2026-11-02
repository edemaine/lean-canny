/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedStepHeight
public import LeanCanny.Algebra.IntegralMixedFullHeightControls
/-! # A bank-height ceiling for actual changing-source script runs

Each instruction's source and syntax are bounded at its chronological stage.
The actual transition bound is derived for every command kind, rather than
postulated as a recurrence. The resulting height and logarithmic size have
native binary controls from fixed original parameters and a unary birth count.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedStepHeight
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript

def height (n S B W D L F C j : ℕ) : ℕ := growth n S B W D L F^j*(C+1)

theorem height_step (n S B W D L F C j : ℕ) :
    height n S B W D L F C (j+1)=growth n S B W D L F*height n S B W D L F C j := by
  unfold height
  rw [pow_succ']
  exact Nat.mul_assoc _ _ _

theorem height_positive (n S B W D L F C j : ℕ) : 1≤height n S B W D L F C j := by
  have HP := Nat.one_le_pow j _ (growth_pos n S B W D L F)
  unfold height
  nlinarith

def ScriptBounds {n B : ℕ} (S W D L F C : ℕ) : List (Instruction n B) → Prop
  | [] => True
  | c::cs => ScriptBounds S W D L F C cs ∧ InstructionBounds (height n S B W D L F C cs.length) F W D L c

theorem run_bounds {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (cs : List (Instruction n B)) (hcs : cs.length≤S+1)
    (W D L F C : ℕ) (hb : ScriptBounds S W D L F C cs) :
    (IntegralMixedFramedHistoryScript.run initial cs hcs).bank.Bounds (height n S B W D L F C cs.length) := by
  induction cs with
  | nil => exact ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | cons c cs ih =>
    have ht : cs.length≤S+1 := by simp only [List.length_cons] at hcs; omega
    have hm : cs.length≤S := by simp only [List.length_cons] at hcs; omega
    have Htail := ih ht hb.1
    have Hstep := step_bounds (IntegralMixedFramedHistoryScript.run initial cs ht) hm c
      (height n S B W D L F C cs.length) F W D L Htail
      (height_positive n S B W D L F C cs.length) hb.2
    change (IntegralMixedFramedHistoryScript.run initial (c::cs) hcs).bank.Bounds
      (height n S B W D L F C (cs.length+1))
    rw [height_step]
    exact Hstep

theorem growth_binary {n S B W D L F : List Bool → ℕ}
    (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B) (hW : UnaryFn W)
    (hD : BinaryFn D) (hL : BinaryFn L) (hF : BinaryFn F) :
    BinaryFn (fun q => growth (n q) (S q) (B q) (W q) (D q) (L q) (F q)) :=
  (IntegralMixedFullScriptHeight.growth_binary hn hS hB hW hD hL).mul (hF.add (BinaryFn.const 2))

theorem height_binary {n S B W D L F C j : List Bool → ℕ}
    (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B) (hW : UnaryFn W)
    (hD : BinaryFn D) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hj : UnaryFn j) :
    BinaryFn (fun q => height (n q) (S q) (B q) (W q) (D q) (L q) (F q) (C q) (j q)) :=
  ((growth_binary hn hS hB hW hD hL hF).powUnary hj).mul (hC.add (BinaryFn.const 1))

theorem height_bits (n S B W D L F C j : ℕ) :
    (height n S B W D L F C j).size≤(growth n S B W D L F).size*j+(C+1).size+1 := by
  have HG : growth n S B W D L F^j≤2^((growth n S B W D L F).size*j) := by
    simpa only [← pow_mul] using Nat.pow_le_pow_left (Nat.lt_size_self (growth n S B W D L F)).le j
  have HH : height n S B W D L F C j≤2^((growth n S B W D L F).size*j+(C+1).size) :=
    (Nat.mul_le_mul HG (Nat.lt_size_self (C+1)).le).trans_eq (pow_add _ _ _).symm
  simpa only [Nat.size_pow] using Nat.size_le_size HH

end LeanCanny.Algebra.IntegralMixedFramedStepHeight

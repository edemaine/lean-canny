/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRunHeight
public import LeanCanny.Algebra.IntegralMixedFramedHistoryFamily
/-! # Actual total framed prefixes inherit the original bank-height schedule

Dropping newer instructions preserves chronological source bounds. Beyond the
script end, the original default source is reused under the growing schedule.
Thus the actual family banks are bounded from full-script syntax and one
original default-instruction bound, without an all-query bank-height premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedStepHeight
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical

theorem instruction_bounds_mono {n B G G' F W D L : ℕ} {c : Instruction n B}
    (hG : G≤G') (hc : InstructionBounds G F W D L c) : InstructionBounds G' F W D L c := by
  have HC : F*G+1≤F*G'+1 := Nat.add_le_add_right (Nat.mul_le_mul_left F hG) 1
  exact ⟨fun e => (hc.low e).trans (Nat.pow_le_pow_right (by decide) HC),hc.leading.trans HC,
    hc.width,hc.degree,hc.auxiliary,command_bounds_mono HC c.command hc.command⟩

theorem source_le_height (n S B W D L F C j : ℕ) : C+1≤height n S B W D L F C j := by
  have HP := Nat.one_le_pow j _ (growth_pos n S B W D L F)
  unfold height
  nlinarith

theorem script_bounds_drop {n S B W D L F C : ℕ} {cs : List (Instruction n B)}
    (hb : ScriptBounds S W D L F C cs) (k : ℕ) : ScriptBounds S W D L F C (cs.drop k) := by
  induction cs generalizing k with
  | nil => simp only [List.drop_nil,ScriptBounds]
  | cons c cs ih =>
    cases k with
    | zero => exact hb
    | succ k => exact ih hb.1 k

theorem script_bounds_past {n S B W D L F C : ℕ} {cs : List (Instruction n B)}
    (hb : ScriptBounds S W D L F C cs) (birth : ℕ) : ScriptBounds S W D L F C (past cs birth) := by
  rw [past,List.take_reverse,List.reverse_reverse]
  exact script_bounds_drop hb _

theorem script_bounds_pad {n S B W D L F C : ℕ} {cs : List (Instruction n B)}
    (hb : ScriptBounds S W D L F C cs) (default : Instruction n B)
    (hd : InstructionBounds (C+1) F W D L default) (k : ℕ) :
    ScriptBounds S W D L F C (List.replicate k default++cs) := by
  induction k with
  | zero => exact hb
  | succ k ih =>
    refine ⟨ih,?_⟩
    exact instruction_bounds_mono (source_le_height n S B W D L F C _) hd

theorem padded_bounds {n S B W D L F C : ℕ} {cs : List (Instruction n B)}
    (hb : ScriptBounds S W D L F C cs) (default : Instruction n B)
    (hd : InstructionBounds (C+1) F W D L default) (birth : ℕ) :
    ScriptBounds S W D L F C (paddedPast default cs birth) :=
  script_bounds_pad (script_bounds_past hb birth) default hd _

theorem padded_run_bounds {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (default : Instruction n B) (cs : List (Instruction n B))
    (birth : ℕ) (hbirth : (paddedPast default cs birth).length≤S+1) (W D L F C : ℕ)
    (hb : ScriptBounds S W D L F C cs) (hd : InstructionBounds (C+1) F W D L default) :
    (IntegralMixedFramedHistoryScript.run initial (paddedPast default cs birth) hbirth).bank.Bounds
      (height n S B W D L F C birth) := by
  have H := run_bounds initial (paddedPast default cs birth) hbirth W D L F C (padded_bounds hb default hd birth)
  simpa only [paddedPast_length] using H

theorem instruction_bounds_get {n S B W D L F C : ℕ} {cs : List (Instruction n B)}
    (hb : ScriptBounds S W D L F C cs) (i : Fin cs.length) :
    InstructionBounds (height n S B W D L F C (cs.length-1-i.val)) F W D L cs[i] := by
  induction cs with
  | nil => exact Fin.elim0 i
  | cons c cs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hb.2
    · have HE : (c::cs).length-1-j.succ.val=cs.length-1-j.val := by
        simp only [List.length_cons,Fin.val_succ]
        omega
      change InstructionBounds (height n S B W D L F C ((c::cs).length-1-j.succ.val)) F W D L cs[j]
      rw [HE]
      exact ih hb.1 j

theorem instruction_bounds_current {n S B W D L F C : ℕ} {cs : List (Instruction n B)}
    (hb : ScriptBounds S W D L F C cs) (default : Instruction n B)
    (hd : InstructionBounds (C+1) F W D L default) (birth : ℕ) :
    InstructionBounds (height n S B W D L F C birth) F W D L ((chronological cs birth).getD default) := by
  by_cases hbirth : birth<cs.length
  · let i : Fin cs.length := ⟨cs.length-1-birth,by omega⟩
    have HE : chronological cs birth=some cs[i] := by
      unfold chronological
      rw [List.getElem?_reverse' (i:=birth) (j:=i.val) (by dsimp only [i]; omega)]
      exact List.getElem?_eq_getElem i.isLt
    rw [HE]
    have HB := instruction_bounds_get hb i
    have HI : cs.length-1-i.val=birth := by dsimp only [i]; omega
    simpa only [HI,Option.getD_some] using HB
  · have HE : chronological cs birth=none := by
      unfold chronological
      exact List.getElem?_eq_none (by rw [List.length_reverse]; omega)
    rw [HE]
    exact instruction_bounds_mono (source_le_height n S B W D L F C birth) hd

open IntegralCriticalHistoryTask

structure FamilyInputs (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (L F C : List Bool → ℕ) : Prop where
  script : ∀ root, ScriptBounds (P.cap root+1) (P.sourceWidth root) (P.degree root) (L root) (F root) (C root) (D.rules root)
  default : ∀ root, InstructionBounds (C root+1) (F root) (P.sourceWidth root) (P.degree root) (L root)
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root)

def familyHeight (P : Parameters) (L F C : List Bool → ℕ) (key : List Bool) : ℕ :=
  height (P.ambient (pairFst key)) (P.cap (pairFst key)+1) (P.width (pairFst key))
    (P.sourceWidth (pairFst key)) (P.degree (pairFst key)) (L (pairFst key)) (F (pairFst key)) (C (pairFst key))
    (IntegralMixedFullHistoryFamilyBits.prefixLength P key)

theorem family_instruction_bounds (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (L F C : List Bool → ℕ) (h : FamilyInputs P D L F C) (key : List Bool) :
    InstructionBounds (familyHeight P L F C key) (F (pairFst key)) (P.sourceWidth (pairFst key))
      (P.degree (pairFst key)) (L (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.instruction P D key) :=
  instruction_bounds_current (h.script _) _ (h.default _) _

theorem family_bank_bounds (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ)
    (h : FamilyInputs P D L F C) (key : List Bool) :
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).bank.Bounds (familyHeight P L F C key) := by
  exact padded_run_bounds (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst key))
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key)) (D.rules (pairFst key))
    (IntegralMixedFullHistoryFamilyBits.prefixLength P key) _ (P.sourceWidth (pairFst key)) (P.degree (pairFst key))
    (L (pairFst key)) (F (pairFst key)) (C (pairFst key)) (h.script _) (h.default _)

theorem family_charged_bank_bounds (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ)
    (h : FamilyInputs P D L F C) (key : List Bool) :
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).bank.Bounds
      ((F (pairFst key)+2)*familyHeight P L F C key) :=
  (family_bank_bounds P D H L F C h key).mono (by nlinarith)

theorem familyHeight_binary (P : Parameters) (a : Access P) {L F C : List Bool → ℕ}
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : BinaryFn (familyHeight P L F C) :=
  height_binary (a.ambient.comp pairFst_mem_FP) ((a.cap.add (UnaryFn.const 1)).comp pairFst_mem_FP)
    (a.width.comp pairFst_mem_FP) (a.sourceWidth.comp pairFst_mem_FP) (a.degree.comp pairFst_mem_FP)
    (hL.comp pairFst_mem_FP) (hF.comp pairFst_mem_FP) (hC.comp pairFst_mem_FP)
    (IntegralMixedFullHistoryFamilyBits.prefix_unary P a)

end LeanCanny.Algebra.IntegralMixedFramedStepHeight

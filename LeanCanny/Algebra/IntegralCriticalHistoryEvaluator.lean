/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalHistoryTask
public import LeanCanny.Algebra.MatrixPowerEncoding
public import LeanCanny.Computation.ControllerRequests

/-! # Compiling the bounded critical-history task graph

A single resumable controller can call any lower-ranked phase or birth.
The compiler derives task closure, a unary rank bound, and a polynomial
frame bound from the flat task format. Local contracts refer to the actual
residue values, with no recursive evaluator or child space certificate.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalHistoryEvaluator
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

/-- Every malformed modulus field still denotes a bounded positive modulus. -/
theorem modulus_le (F : Parameters) (q : List Bool) :
    IntegralCriticalHistoryTask.modulus F q ≤ numericCap F (RankedHistoryTask.root q) := by
  unfold IntegralCriticalHistoryTask.modulus
  split_ifs
  · exact numericCap_pos F _
  · exact get_le F .modulus q

def residueWidth (F : Parameters) (q : List Bool) : ℕ := (numericCap F (RankedHistoryTask.root q)).size

theorem residueWidth_unary (F : Parameters) (a : Access F) : UnaryFn (residueWidth F) :=
  ((UnaryFn.length (numericCap_binary F a).bits_mem_FP).of_eq
    (fun _q => BinaryNatCode.length_encode _)).comp RankedHistoryTask.root_FP

theorem answer_length (F : Parameters)
    (x : (q : List Bool) → ZMod (IntegralCriticalHistoryTask.modulus F q)) (q : List Bool) :
    (residueBits (x q)).length ≤ residueWidth F q := by
  let : NeZero (IntegralCriticalHistoryTask.modulus F q) := ⟨modulus_ne_zero F q⟩
  exact (residueBits_length_le _ _).trans (Nat.size_le_size (modulus_le F q))

def spaceBudget (F : Parameters) (factor : ℕ) (localBound : List Bool → ℕ) (q : List Bool) : ℕ :=
  (factor + 1) * taskBudget F q + localBound (RankedHistoryTask.root q) + residueWidth F q

theorem spaceBudget_unary (F : Parameters) (a : Access F) (factor : ℕ)
    (localBound : List Bool → ℕ) (hB : UnaryFn localBound) : UnaryFn (spaceBudget F factor localBound) :=
  (((UnaryFn.const (factor + 1)).mul (taskBudget_unary F a)).add
    (hB.comp RankedHistoryTask.root_FP)).add (residueWidth_unary F a)

/-- Only local controller operations carry machine certificates. Recursive
calls are discharged by the flat graph's rank and frame bounds. -/
theorem evaluator {S : Type} [Inhabited S] {encS : S ↪ List Bool}
    (F : Parameters) (a : Access F) (C : RecursiveController.Controller (List Bool) S)
    (hC : C.Certificates (encQ := encBits) (encS := encS))
    (x : (q : List Bool) → ZMod (IntegralCriticalHistoryTask.modulus F q))
    (budget clock localBound : List Bool → ℕ) (factor : ℕ)
    (hclock : BinaryFn clock) (hlocal : UnaryFn localBound)
    (hstop : ∀ q, C.halted ((C.reference (fun q => residueBits (x q)))^[budget q] (C.initial q)) = true)
    (hbudget : ∀ q, budget q ≤ clock (RankedHistoryTask.root q))
    (hdone : ∀ q t, t ≤ budget q →
      C.halted ((C.reference (fun q => residueBits (x q)))^[t] (C.initial q)) = true →
      C.output ((C.reference (fun q => residueBits (x q)))^[t] (C.initial q)) = residueBits (x q))
    (hchild : ∀ q child, C.Requests (fun q => residueBits (x q)) budget q child →
      RankedHistoryTask.root child = RankedHistoryTask.root q ∧ child.length ≤ wordBudget F q ∧ rank F child < rank F q)
    (hstate : ∀ q t, t ≤ budget q →
      (encS ((C.reference (fun q => residueBits (x q)))^[t] (C.initial q))).length ≤
        factor * q.length + localBound (RankedHistoryTask.root q)) :
    SpaceFunction (fun q => residueBits (x q)) := by
  have HB : PolyBounded (fun q => (encBits q).length) (spaceBudget F factor localBound) := by
    simpa only [encBits_apply, encUnary_apply, List.length_replicate] using
      (spaceBudget_unary F a factor localBound hlocal).polyBounded_length
  refine ⟨C.evaluatorOfOrbits hC (fun q => residueBits (x q)) (rank F) budget (Tasks F)
    (clock ∘ RankedHistoryTask.root) (rankBudget F) (spaceBudget F factor localBound)
    (hclock.comp RankedHistoryTask.root_FP) (rankBudget_unary F a) HB (tasks_self F)
    (fun _ q _ => hstop q) ?_ (fun _ q t _ ht hh => hdone q t ht hh) ?_ ?_ ?_ ?_ ?_⟩
  · intro r q hq
    have H := hbudget q
    rw [tasks_root F hq] at H
    exact H
  · intro r q t hq ht hh hn
    obtain ⟨hr, hl, hd⟩ := hchild q _ ⟨t, ht, hh, hn, rfl⟩
    exact ⟨Or.inr ⟨hr.trans (tasks_root F hq), hl.trans_eq (wordBudget_eq F (tasks_root F hq))⟩, hd⟩
  · intro r q hq
    exact (tasks_rank F hq).le
  · intro r q hq
    have H := tasks_length F hq
    have HM : taskBudget F r ≤ (factor + 1) * taskBudget F r := by
      exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    exact H.trans (HM.trans (by unfold spaceBudget; omega))
  · intro r q hq t ht
    have H := hstate q t ht
    rw [tasks_root F hq] at H
    have HL := Nat.mul_le_mul_left factor (tasks_length F hq)
    unfold spaceBudget
    rw [Nat.add_mul]
    omega
  · intro r q hq
    have H := answer_length F x q
    have HE : residueWidth F q = residueWidth F r := by
      unfold residueWidth
      rw [tasks_root F hq]
    rw [HE] at H
    exact H.trans (by unfold spaceBudget; omega)

end LeanCanny.Algebra.IntegralCriticalHistoryEvaluator

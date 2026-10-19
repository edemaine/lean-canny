/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerControllerCorrect

/-!
# The first halting time and terminal answer of matrix powering

The potential of every iterate is the initial potential minus elapsed steps.
This proves that the controller cannot signal completion before the specified
clock, in addition to the existing exact final-result theorem.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower
open Complexity

variable {R : Type*} [Semiring R] {n : ℕ}

def isDone : State R n → Bool
  | .done _ => true
  | _ => false

omit [Semiring R] in
theorem isDone_iff_stateWork_zero (s : State R n) : isDone s = true ↔ stateWork s = 0 := by
  constructor
  · intro h
    cases s <;> simp_all [isDone, stateWork]
  · intro h
    obtain ⟨x, rfl⟩ := stateWork_zero s h
    rfl

theorem step_stateWork (A : Matrix (Fin n) (Fin n) R) (s : State R n) :
    stateWork (MatrixPower.step A s) = stateWork s - 1 := by
  by_cases h : stateWork s = 0
  · obtain ⟨x, rfl⟩ := stateWork_zero s h
    rfl
  · have hs : ∀ x, s ≠ .done x := by
      intro x hx
      subst s
      exact h rfl
    have hstep := step_work A s hs
    omega

theorem iterate_stateWork (A : Matrix (Fin n) (Fin n) R) (t : ℕ) (s : State R n) :
    stateWork ((MatrixPower.step A)^[t] s) = stateWork s - t := by
  induction t with
  | zero => simp
  | succ t ih => rw [Function.iterate_succ_apply', step_stateWork, ih]; omega

theorem run_before (A : Matrix (Fin n) (Fin n) R) (e t : ℕ) (i j : Fin n)
    (ht : t < work n e.size e + 1) :
    isDone ((MatrixPower.step A)^[t] (.eval ⟨e.size, e, i, j⟩ [])) = false := by
  apply Bool.eq_false_iff.mpr
  intro hd
  have hz := (isDone_iff_stateWork_zero _).mp hd
  have hw := iterate_stateWork A t (.eval ⟨e.size, e, i, j⟩ [])
  rw [hz] at hw
  simp only [stateWork, stackWork, Query.work] at hw
  omega

namespace Controller
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets

def halted (packet : List Bool) : Bool := (pairSnd packet)[0]?.getD false

theorem halted_mem_FP : (fun packet => [halted packet]) ∈ FP :=
  getBit_mem_FP pairSnd_mem_FP (UnaryFn.const 0)

omit [Semiring R] in
theorem halted_packet (c : List Bool) (enc : R → List Bool) (s : State R n) :
    halted (pair c (stateBits enc s)) = isDone s := by
  cases s <;> simp [halted, pairSnd_pair, stateBits, isDone]

def zeroAnswer (packet : List Bool) : Bool := decide ((pairSnd packet).drop 1 = [])

theorem zeroAnswer_mem_FP : (fun packet => [zeroAnswer packet]) ∈ FP :=
  (stringEq_fppred (drop_mem_FP pairSnd_mem_FP (UnaryFn.const 1)) (constFn_mem_FP [])).flag_mem_FP

theorem zeroAnswer_done (c : List Bool) (m : ℕ) [NeZero m] (x : ZMod m) :
    zeroAnswer (pair c (stateBits (n := n) residueBits (.done x))) = true ↔ x = 0 := by
  simp only [zeroAnswer, pairSnd_pair, stateBits, List.drop_succ_cons, List.drop_zero,
    decide_eq_true_eq]
  have hz : residueBits (0 : ZMod m) = [] := by simp [residueBits, BinaryNatCode.encode]
  rw [← hz, (residueBits_injective m).eq_iff]

theorem halted_before (ops : Callbacks) (c : List Bool)
    (A : Matrix (Fin n) (Fin n) R) (enc : R → List Bool) (hc : CorrectAt ops c A enc)
    (e t : ℕ) (i j : Fin n) (ht : t < work n e.size e + 1) :
    halted ((step ops)^[t] (pair c (stateBits enc (.eval ⟨e.size, e, i, j⟩ [])))) = false := by
  rw [iterate_packet ops c A enc hc, halted_packet]
  exact run_before A e t i j ht

theorem halted_after (ops : Callbacks) (c : List Bool)
    (A : Matrix (Fin n) (Fin n) R) (enc : R → List Bool) (hc : CorrectAt ops c A enc)
    (e : ℕ) (i j : Fin n) :
    halted ((step ops)^[work n e.size e + 1]
      (pair c (stateBits enc (.eval ⟨e.size, e, i, j⟩ [])))) = true := by
  rw [run_pow ops c A enc hc]
  simp [halted_packet, isDone]

end Controller
end LeanCanny.Algebra.MatrixPower

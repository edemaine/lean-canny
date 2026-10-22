/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerSpaceEntries
public import LeanCanny.Computation.RecursiveControllerSpace

/-! # Matrix powering as a resumable recursive coefficient stage

Entry requests become task queries. The native controller certificate does not
assume a computation certificate for their answers. Its mathematical oracle run
agrees with the existing power controller, including its exact stopping index
and polynomial encoded state bound.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation
open Turing.MultiTapeTM
open Controller

def controller (ops : Callbacks) (init entryTask : List Bool → List Bool) :
    RecursiveController.Controller (List Bool) (List Bool) where
  initial := init
  halted := halted
  output := ModularAccess.valueBits
  needs := needsEntry
  query := entryTask ∘ entryInput
  advance := Controller.step (withoutEntry ops)
  resume := fun p => resumeEntry id (pair p.1 p.2)

theorem certificates (ops : Callbacks) (ho : ops.ControlsPolyTime)
    (init entryTask : List Bool → List Bool) (hi : SpaceFunction init) (he : entryTask ∈ FP) :
    (controller ops init entryTask).Certificates (encQ := encBits) (encS := encBits) := by
  have hquery : (entryTask ∘ entryInput) ∈ FP := mem_FP_comp entryInput_mem_FP he
  refine ⟨hi.computable, .of_polyTime (flag_computable halted_mem_FP),
    .of_polyTime (FP.computable ModularAccess.valueBits_mem_FP),
    .of_polyTime (flag_computable needsEntry_mem_FP),
    .of_polyTime (FP.computable hquery),
    .of_polyTime (FP.computable (step_mem_FP _ (withoutEntry_polyTime ops ho))), ?_⟩
  have hp := pair_computable (ComputableTidilyInPolyTime.fst encBits encBits)
    (ComputableTidilyInPolyTime.snd encBits encBits)
  exact .of_polyTime ((FP.computable (resumeEntry_mem_FP id_mem_FP)).comp hp)

def oracleCallbacks (ops : Callbacks) (entryTask answer : List Bool → List Bool) : Callbacks :=
  { ops with entry := answer ∘ entryTask }

theorem reference_packet (ops : Callbacks) (init entryTask answer : List Bool → List Bool)
    (c s : List Bool) :
    (controller ops init entryTask).reference answer (pair c s) =
      Controller.step (oracleCallbacks ops entryTask answer) (pair c s) := by
  let p := pair c s
  change (controller ops init entryTask).reference answer p = Controller.step (oracleCallbacks ops entryTask answer) p
  by_cases hh : halted p = true
  · have hh' : (pairSnd p)[0]?.getD false = true := hh
    change (if halted p then p else _) = Controller.step (oracleCallbacks ops entryTask answer) p
    simp only [hh, ite_true, Controller.step, nextState, hh']
    simp only [p, pairFst_pair, pairSnd_pair]
  · have hh' : halted p = false := Bool.eq_false_iff.mpr hh
    by_cases hn : needsEntry p = true
    · have he := resumeEntry_eq_step (oracleCallbacks ops entryTask answer) id p
        (answer (entryTask (entryInput p))) hn rfl
      simpa only [RecursiveController.Controller.reference, controller, hh', Bool.false_eq_true,
        ite_false, hn, ite_true, Function.comp_apply] using he
    · have hn' : needsEntry p = false := Bool.eq_false_iff.mpr hn
      have he := step_withoutEntry (oracleCallbacks ops entryTask answer) p hn'
      simpa only [RecursiveController.Controller.reference, controller, hh', hn', Bool.false_eq_true,
        ite_false, withoutEntry, oracleCallbacks] using he

variable {R : Type} [Semiring R] {n : ℕ}

theorem reference_iterate (ops : Callbacks) (init entryTask answer : List Bool → List Bool)
    (c : List Bool) (A : Matrix (Fin n) (Fin n) R) (enc : R → List Bool)
    (hc : CorrectAt (oracleCallbacks ops entryTask answer) c A enc) (t : ℕ) (s : State R n) :
    ((controller ops init entryTask).reference answer)^[t] (pair c (stateBits enc s)) =
      pair c (stateBits enc ((MatrixPower.step A)^[t] s)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih,
      reference_packet ops init entryTask answer,
      step_packet _ c A enc hc, Function.iterate_succ_apply']

theorem halted_after (ops : Callbacks) (init entryTask answer : List Bool → List Bool)
    (c : List Bool) (A : Matrix (Fin n) (Fin n) R) (enc : R → List Bool)
    (hc : CorrectAt (oracleCallbacks ops entryTask answer) c A enc) (e : ℕ) (i j : Fin n)
    (hi : init c = pair c (stateBits enc (.eval ⟨e.size, e, i, j⟩ []))) :
    (controller ops init entryTask).halted
      (((controller ops init entryTask).reference answer)^[work n e.size e + 1] (init c)) = true := by
  rw [hi, reference_iterate ops init entryTask answer c A enc hc, MatrixPower.run_pow]
  exact halted_packet c enc (.done ((A ^ e) i j))

theorem output_when_halted (ops : Callbacks) (init entryTask answer : List Bool → List Bool)
    (c : List Bool) (A : Matrix (Fin n) (Fin n) R) (enc : R → List Bool)
    (hc : CorrectAt (oracleCallbacks ops entryTask answer) c A enc) (e t : ℕ) (i j : Fin n)
    (hi : init c = pair c (stateBits enc (.eval ⟨e.size, e, i, j⟩ [])))
    (hh : (controller ops init entryTask).halted
      (((controller ops init entryTask).reference answer)^[t] (init c)) = true) :
    (controller ops init entryTask).output
      (((controller ops init entryTask).reference answer)^[t] (init c)) = enc ((A ^ e) i j) := by
  rw [hi, reference_iterate ops init entryTask answer c A enc hc] at hh ⊢
  change halted (pair c (stateBits enc ((MatrixPower.step A)^[t] (.eval ⟨e.size, e, i, j⟩ [])))) = true at hh
  rw [halted_packet] at hh
  have hv := iterate_value A t (.eval ⟨e.size, e, i, j⟩ [])
  change value A ((MatrixPower.step A)^[t] (.eval ⟨e.size, e, i, j⟩ [])) =
    entry A e.size e i j at hv
  rw [entry_size_eq_pow] at hv
  generalize heq : (MatrixPower.step A)^[t] (.eval ⟨e.size, e, i, j⟩ []) = s at hh hv ⊢
  cases s with
  | eval q stack => simp only [isDone, Bool.false_eq_true] at hh
  | ret x stack => simp only [isDone, Bool.false_eq_true] at hh
  | done x =>
    change x = (A ^ e) i j at hv
    simpa only [controller, ModularAccess.valueBits_done] using congrArg enc hv

omit [Semiring R] in
theorem entry_query_indices (c : List Bool) (enc : R → List Bool) (s : State R n)
    (hn : needsEntry (pair c (stateBits enc s)) = true) :
    ∃ i j : Fin n, entryInput (pair c (stateBits enc s)) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
  cases s with
  | eval q stack =>
    refine ⟨q.row, q.col, ?_⟩
    simp only [entryInput, payload, body, stateBits, pairFst_pair, pairSnd_pair,
      List.drop_succ_cons, List.drop_zero, row_queryBits, col_queryBits]
  | ret x stack => simp [needsEntry, stateBits] at hn
  | done x => simp [needsEntry, stateBits] at hn

theorem modular_state_length (dimension modulus init entryTask answer : List Bool → List Bool)
    (c : List Bool) (m : ℕ) [NeZero m] (A : Matrix (Fin n) (Fin n) (ZMod m))
    (hc : CorrectAt (oracleCallbacks (modularCallbacks dimension modulus (fun _ => [])) entryTask answer) c A residueBits)
    (e t : ℕ) (i j : Fin n)
    (hi : init c = pair c (stateBits (residueBits (m := m)) (.eval ⟨e.size, e, i, j⟩ []))) :
    (((controller (modularCallbacks dimension modulus (fun _ => [])) init entryTask).reference answer)^[t]
      (init c)).length ≤ 2 * c.length + 2 + 64 * (n.size + e.size + m.size + 1) ^ 2 := by
  rw [hi, reference_iterate _ init entryTask answer c A residueBits hc]
  have h := modular_run_length_le dimension modulus (answer ∘ entryTask) c m A hc e t i j
  have hc' : CorrectAt (modularCallbacks dimension modulus (answer ∘ entryTask)) c A residueBits := hc
  rw [iterate_packet _ c A residueBits hc'] at h
  exact h

end LeanCanny.Algebra.MatrixPower.RecursiveStage

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBerkowitzBlockSpace
public import LeanCanny.Algebra.MatrixPowerModularRecursiveStage

/-! # A resumable evaluator of actual relative characteristic coefficients

The constructed integer block-power matrix is streamed by child tasks.
Out-of-range coefficients return zero after the same bounded computation.
The stored context supplies this output guard without another saved frame.
The spatial characteristic degree stays independent of the old algebra rank.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBerkowitzBlockBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

noncomputable def base (S : Source) (a : Access S) (task : List Bool → List Bool) :
    RecursiveController.Controller (List Bool) (List Bool) :=
  ModularRecursiveStage.stage (powerAccess S a) task

noncomputable def output (S : Source) (s : List Bool) : List Bool :=
  if S.coefficient (pairFst s) ≤ S.dimension (pairFst s) then ModularAccess.valueBits s else []

noncomputable def controller (S : Source) (a : Access S) (task : List Bool → List Bool) :
    RecursiveController.Controller (List Bool) (List Bool) := { base S a task with output := output S }

theorem output_FP (S : Source) (a : Access S) : output S ∈ FP := by
  have HC : BinaryFn (fun s => S.coefficient (pairFst s)) := a.coefficient.comp pairFst_mem_FP
  have HD : BinaryFn (fun s => S.dimension (pairFst s)) := a.dimension.comp pairFst_mem_FP
  exact (HC.le HD).ite_mem_FP ModularAccess.valueBits_mem_FP (constFn_mem_FP [])

theorem certificates (S : Source) (a : Access S) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (controller S a task).Certificates (encQ := encBits) (encS := encBits) := by
  obtain ⟨hi, hh, _ho, hn, hq, ha, hr⟩ := ModularRecursiveStage.certificates (powerAccess S a) (power_controls S a) task ht
  exact ⟨hi, hh, .of_tidyPolyTime (FP.computable (output_FP S a)), hn, hq, ha, hr⟩

theorem reply_correct (S : Source) (_a : Access S) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin (powerDimension S c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((S.powerMatrix c i j : ℤ) : ZMod (S.modulus c))) :
    ∀ c (i j : Fin ((powerFamily S).dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits ((powerFamily S).matrix c i j) := by
  intro c i j
  exact he c i j

theorem reference_eq (S : Source) (a : Access S) (task answer : List Bool → List Bool) :
    (controller S a task).reference answer = (base S a task).reference answer := rfl

theorem clock_binary (S : Source) (a : Access S) : BinaryFn (ModularRecursiveStage.clock (powerFamily S)) :=
  ModularRecursiveStage.clock_binary (powerAccess S a) (power_controls S a)

theorem stateBound_unary (S : Source) (a : Access S) : UnaryFn (ModularRecursiveStage.stateBound (powerFamily S)) :=
  ModularRecursiveStage.stateBound_unary (powerAccess S a) (power_controls S a)

theorem halted_after (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin (powerDimension S c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((S.powerMatrix c i j : ℤ) : ZMod (S.modulus c))) (c : List Bool) :
    (controller S a task).halted (((controller S a task).reference answer)^[ModularRecursiveStage.clock (powerFamily S) c]
      ((controller S a task).initial c)) = true := by
  rw [reference_eq]
  exact ModularRecursiveStage.halted_after (powerAccess S a) task answer (reply_correct S a task answer he) c

theorem output_when_halted (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin (powerDimension S c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((S.powerMatrix c i j : ℤ) : ZMod (S.modulus c))) (c : List Bool) (t : ℕ)
    (hh : (controller S a task).halted (((controller S a task).reference answer)^[t] ((controller S a task).initial c)) = true) :
    (controller S a task).output (((controller S a task).reference answer)^[t] ((controller S a task).initial c)) = S.value c := by
  rw [reference_eq] at hh ⊢
  change output S (((base S a task).reference answer)^[t] ((base S a task).initial c)) = _
  unfold output
  have HC : pairFst (((base S a task).reference answer)^[t] ((base S a task).initial c)) = c :=
    ModularRecursiveStage.context_iterate (powerAccess S a) task answer (reply_correct S a task answer he) c t
  rw [HC]
  by_cases hk : S.coefficient c ≤ S.dimension c
  · rw [ite_eq_left hk]
    exact (ModularRecursiveStage.output_when_halted (powerAccess S a) task answer (reply_correct S a task answer he) c t hh).trans
      (power_value S c hk)
  · rw [ite_eq_right hk]
    exact (high_value S c (by omega)).symm

theorem state_length (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin (powerDimension S c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((S.powerMatrix c i j : ℤ) : ZMod (S.modulus c))) (c : List Bool) (t : ℕ) :
    (((controller S a task).reference answer)^[t] ((controller S a task).initial c)).length ≤
      ModularRecursiveStage.stateBound (powerFamily S) c := by
  rw [reference_eq]
  exact ModularRecursiveStage.state_length (powerAccess S a) task answer (reply_correct S a task answer he) c t

theorem requests_in_bounds (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin (powerDimension S c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((S.powerMatrix c i j : ℤ) : ZMod (S.modulus c)))
    (budget : List Bool → ℕ) (c child : List Bool)
    (hreq : (controller S a task).Requests answer budget c child) :
    ∃ i j : Fin (powerDimension S c), child = task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) :=
  ModularRecursiveStage.requests_in_bounds (powerAccess S a) task answer (reply_correct S a task answer he) budget c child hreq

end LeanCanny.Algebra.IntegralBerkowitzBlockBits.RecursiveStage

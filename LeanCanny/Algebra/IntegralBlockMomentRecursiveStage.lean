/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBlockMomentSpace
public import LeanCanny.Algebra.MatrixPowerModularRecursiveStage

/-! # Resumable powering for actual algebra-valued moment coefficients

The augmented integer block matrix is streamed by child tasks. Native
metadata supplies the controller certificate, a binary stopping allowance,
and a unary space bound. No row, column, or matrix evaluator is assumed.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBlockMomentBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

noncomputable def controller (F : Family) (a : Access F) (task : List Bool → List Bool) :
    RecursiveController.Controller (List Bool) (List Bool) :=
  ModularRecursiveStage.stage (powerAccess F a) task

theorem certificates (F : Family) (a : Access F) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (controller F a task).Certificates (encQ := encBits) (encS := encBits) :=
  ModularRecursiveStage.certificates (powerAccess F a) (power_controls F a) task ht

theorem reply_correct (F : Family) (_a : Access F) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin ((F.dimension c + 2) * F.rank c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((F.powerMatrix c i j : ℤ) : ZMod (F.modulus c))) :
    ∀ c (i j : Fin ((powerFamily F).dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits ((powerFamily F).matrix c i j) := he

theorem clock_binary (F : Family) (a : Access F) : BinaryFn (ModularRecursiveStage.clock (powerFamily F)) :=
  ModularRecursiveStage.clock_binary (powerAccess F a) (power_controls F a)

theorem stateBound_unary (F : Family) (a : Access F) : UnaryFn (ModularRecursiveStage.stateBound (powerFamily F)) :=
  ModularRecursiveStage.stateBound_unary (powerAccess F a) (power_controls F a)

theorem halted_after (F : Family) (a : Access F) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin ((F.dimension c + 2) * F.rank c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((F.powerMatrix c i j : ℤ) : ZMod (F.modulus c))) (c : List Bool) :
    (controller F a task).halted (((controller F a task).reference answer)^[ModularRecursiveStage.clock (powerFamily F) c]
      ((controller F a task).initial c)) = true :=
  ModularRecursiveStage.halted_after (powerAccess F a) task answer (reply_correct F a task answer he) c

theorem output_when_halted (F : Family) (a : Access F) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin ((F.dimension c + 2) * F.rank c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((F.powerMatrix c i j : ℤ) : ZMod (F.modulus c))) (c : List Bool) (t : ℕ)
    (hh : (controller F a task).halted (((controller F a task).reference answer)^[t] ((controller F a task).initial c)) = true) :
    (controller F a task).output (((controller F a task).reference answer)^[t] ((controller F a task).initial c)) = F.value c :=
  (ModularRecursiveStage.output_when_halted (powerAccess F a) task answer (reply_correct F a task answer he) c t hh).trans
    (congrFun (power_value F) c)

theorem state_length (F : Family) (a : Access F) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin ((F.dimension c + 2) * F.rank c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((F.powerMatrix c i j : ℤ) : ZMod (F.modulus c))) (c : List Bool) (t : ℕ) :
    (((controller F a task).reference answer)^[t] ((controller F a task).initial c)).length ≤
      ModularRecursiveStage.stateBound (powerFamily F) c :=
  ModularRecursiveStage.state_length (powerAccess F a) task answer (reply_correct F a task answer he) c t

theorem requests_in_bounds (F : Family) (a : Access F) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin ((F.dimension c + 2) * F.rank c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((F.powerMatrix c i j : ℤ) : ZMod (F.modulus c)))
    (budget : List Bool → ℕ) (c child : List Bool)
    (hreq : (controller F a task).Requests answer budget c child) :
    ∃ i j : Fin ((F.dimension c + 2) * F.rank c), child = task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) :=
  ModularRecursiveStage.requests_in_bounds (powerAccess F a) task answer (reply_correct F a task answer he) budget c child hreq

end LeanCanny.Algebra.IntegralBlockMomentBits.RecursiveStage

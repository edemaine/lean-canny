/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralBlockPowerRecursiveStage
public import LeanCanny.Algebra.MatrixPowerModularRecursiveStageLocal
/-! # Block powering requires replies only at its current context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralBlockPowerBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

abbrev RepliesAt (F : Family) (task answer : List Bool → List Bool) (c : List Bool) : Prop :=
  ∀ i j : Fin (F.dimension c * F.rank c), answer (task (pair c
    (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits ((F.powerMatrix c i j : ℤ) : ZMod (F.modulus c))

theorem halted_after_local (F : Family) (a : Access F) (task answer : List Bool → List Bool)
    (c : List Bool) (he : RepliesAt F task answer c) :
    (controller F a task).halted (((controller F a task).reference answer)^[ModularRecursiveStage.clock (powerFamily F) c]
      ((controller F a task).initial c)) = true :=
  ModularRecursiveStage.halted_after_local (powerAccess F a) task answer c he

theorem output_when_halted_local (F : Family) (a : Access F) (task answer : List Bool → List Bool)
    (c : List Bool) (he : RepliesAt F task answer c) (t : ℕ)
    (hh : (controller F a task).halted (((controller F a task).reference answer)^[t] ((controller F a task).initial c)) = true) :
    (controller F a task).output (((controller F a task).reference answer)^[t] ((controller F a task).initial c)) = F.value c :=
  (ModularRecursiveStage.output_when_halted_local (powerAccess F a) task answer c he t hh).trans
    (congrFun (power_value F) c)

theorem state_length_local (F : Family) (a : Access F) (task answer : List Bool → List Bool)
    (c : List Bool) (he : RepliesAt F task answer c) (t : ℕ) :
    (((controller F a task).reference answer)^[t] ((controller F a task).initial c)).length ≤
      ModularRecursiveStage.stateBound (powerFamily F) c :=
  ModularRecursiveStage.state_length_local (powerAccess F a) task answer c he t

theorem requests_in_bounds_local (F : Family) (a : Access F) (task answer : List Bool → List Bool)
    (c : List Bool) (he : RepliesAt F task answer c) (budget : List Bool → ℕ) (child : List Bool)
    (hc : (controller F a task).Requests answer budget c child) :
    ∃ i j : Fin (F.dimension c * F.rank c), child = task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) :=
  ModularRecursiveStage.requests_in_bounds_local (powerAccess F a) task answer c he budget child hc

end LeanCanny.Algebra.IntegralBlockPowerBits.RecursiveStage

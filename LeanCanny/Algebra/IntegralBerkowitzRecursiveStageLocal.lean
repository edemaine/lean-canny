/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralBerkowitzRecursiveStage
public import LeanCanny.Algebra.MatrixPowerModularRecursiveStageLocal
/-! # Relative characteristic powering with replies only at the actual context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralBerkowitzBlockBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
theorem halted_after_local (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ (i j : Fin (powerDimension S c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((S.powerMatrix c i j : ℤ) : ZMod (S.modulus c))) :
    (controller S a task).halted (((controller S a task).reference answer)^[ModularRecursiveStage.clock (powerFamily S) c]
      ((controller S a task).initial c)) = true := by
  rw [reference_eq]
  exact ModularRecursiveStage.halted_after_local (powerAccess S a) task answer c he

theorem output_when_halted_local (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ (i j : Fin (powerDimension S c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((S.powerMatrix c i j : ℤ) : ZMod (S.modulus c))) (t : ℕ)
    (hh : (controller S a task).halted (((controller S a task).reference answer)^[t] ((controller S a task).initial c)) = true) :
    (controller S a task).output (((controller S a task).reference answer)^[t] ((controller S a task).initial c)) = S.value c := by
  rw [reference_eq] at hh ⊢
  change output S (((base S a task).reference answer)^[t] ((base S a task).initial c)) = _
  unfold output
  have HC : pairFst (((base S a task).reference answer)^[t] ((base S a task).initial c)) = c :=
    ModularRecursiveStage.context_iterate_local (powerAccess S a) task answer c he t
  rw [HC]
  by_cases hk : S.coefficient c ≤ S.dimension c
  · rw [ite_eq_left hk]
    exact (ModularRecursiveStage.output_when_halted_local (powerAccess S a) task answer c he t hh).trans
      (power_value S c hk)
  · rw [ite_eq_right hk]
    exact (high_value S c (by omega)).symm

theorem state_length_local (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ (i j : Fin (powerDimension S c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((S.powerMatrix c i j : ℤ) : ZMod (S.modulus c))) (t : ℕ) :
    (((controller S a task).reference answer)^[t] ((controller S a task).initial c)).length ≤
      ModularRecursiveStage.stateBound (powerFamily S) c := by
  rw [reference_eq]
  exact ModularRecursiveStage.state_length_local (powerAccess S a) task answer c he t

theorem requests_in_bounds_local (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ (i j : Fin (powerDimension S c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((S.powerMatrix c i j : ℤ) : ZMod (S.modulus c)))
    (budget : List Bool → ℕ) (child : List Bool)
    (hreq : (controller S a task).Requests answer budget c child) :
    ∃ i j : Fin (powerDimension S c), child = task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) :=
  ModularRecursiveStage.requests_in_bounds_local (powerAccess S a) task answer c he budget child hreq

end LeanCanny.Algebra.IntegralBerkowitzBlockBits.RecursiveStage

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralFrozenPowerController
public import LeanCanny.Computation.TwoCallController

/-! # Recursive frozen constants and actual cleared lower coefficients

The constant spatial coefficient requests the frozen-power sum and scales
it by the FP leading residue. Other coefficients return zero locally.
Two recursive replies then add this constant to the original cleared
coefficient. No retained-height or coefficient evaluator is assumed.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralFrozenPowerBits.ConstantStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] multiplyPost Source.sumValue Source.leadingValue Source.constantValue

noncomputable def finish (S : Source) (a : Access S) (z : List Bool) : List Bool :=
  multiplyPost S (pair (pairFst z) (pair (a.leading (pairFst z)) (pairSnd z)))

theorem finish_FP (S : Source) (a : Access S) (ha : a.leading ∈ FP) : finish S a ∈ FP :=
  mem_FP_comp (mem_FP_pair pairFst_mem_FP (mem_FP_pair (mem_FP_comp pairFst_mem_FP ha) pairSnd_mem_FP))
    (multiplyPost_FP S a)

noncomputable def program (S : Source) (a : Access S) (task : List Bool → List Bool) : SingleCall.Program where
  request c := decide (zeroTarget S c)
  query := task
  immediate _ := []
  finish := finish S a

theorem controls (S : Source) (a : Access S) (ha : a.leading ∈ FP) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (program S a task).Controls :=
  ⟨(zeroTarget_fppred S a).flag_mem_FP, ht, constFn_mem_FP [], finish_FP S a ha⟩

theorem finish_packet (S : Source) (a : Access S) (c : List Bool) :
    finish S a (pair c (S.sumValue c)) = S.leadingValue c := by
  unfold finish
  simp only [pairFst_pair, pairSnd_pair]
  rw [a.leading_eq, Source.sumValue, multiplyPost_packet]
  exact leading_value S c

theorem value_eq (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (he : ∀ c, answer (task c) = S.sumValue c) (c : List Bool) :
    (program S a task).value answer c = S.constantValue c := by
  simp only [SingleCall.Program.value, program, decide_eq_true_eq, he, finish_packet]
  exact constant_value S c

theorem requests_iff (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (c child : List Bool) :
    (program S a task).controller.Requests answer budget c child ↔ zeroTarget S c ∧ child = task c := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

end LeanCanny.Algebra.IntegralFrozenPowerBits.ConstantStage

namespace LeanCanny.Algebra.IntegralFrozenPowerBits.LowerStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addPost Source.lowerValue Source.constantValue IntegralClearedCoefficientBits.Source.value

noncomputable def program (S : Source) (clearedTask constantTask : List Bool → List Bool) : RecursiveFold.Program :=
  TwoCall.program clearedTask constantTask (addPost S)

theorem certificates (S : Source) (a : Access S) (clearedTask constantTask : List Bool → List Bool)
    (hc : clearedTask ∈ FP) (hk : constantTask ∈ FP) :
    (program S clearedTask constantTask).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  TwoCall.certificates _ _ _ hc hk (addPost_FP S a)

theorem value_eq (S : Source) (clearedTask constantTask answer : List Bool → List Bool)
    (hc : ∀ c, answer (clearedTask c) = S.toSource.value c)
    (hk : ∀ c, answer (constantTask c) = S.constantValue c) (c : List Bool) :
    (program S clearedTask constantTask).value answer c = S.lowerValue c := by
  change (TwoCall.program clearedTask constantTask (addPost S)).value answer c = _
  rw [TwoCall.value_eq, hc c, hk c]
  exact lower_value S c

theorem halted_after (S : Source) (clearedTask constantTask answer : List Bool → List Bool) (c : List Bool) :
    (program S clearedTask constantTask).controller.halted
      (((program S clearedTask constantTask).controller.reference answer)^[2]
        ((program S clearedTask constantTask).initial c)) = true :=
  TwoCall.halted_after _ _ _ answer c

theorem output_when_halted (S : Source) (clearedTask constantTask answer : List Bool → List Bool)
    (hc : ∀ c, answer (clearedTask c) = S.toSource.value c)
    (hk : ∀ c, answer (constantTask c) = S.constantValue c) (c : List Bool) (t : ℕ)
    (hh : (program S clearedTask constantTask).controller.halted
      (((program S clearedTask constantTask).controller.reference answer)^[t]
        ((program S clearedTask constantTask).initial c)) = true) :
    (program S clearedTask constantTask).controller.output
      (((program S clearedTask constantTask).controller.reference answer)^[t]
        ((program S clearedTask constantTask).initial c)) = S.lowerValue c :=
  ((program S clearedTask constantTask).output_when_halted answer c t hh).trans (value_eq S _ _ answer hc hk c)

theorem requests_iff (S : Source) (clearedTask constantTask answer : List Bool → List Bool) (c child : List Bool) :
    (program S clearedTask constantTask).controller.Requests answer (fun _ => 2) c child ↔
      child = clearedTask c ∨ child = constantTask c :=
  TwoCall.requests_iff _ _ _ answer c child

theorem state_length (S : Source) (clearedTask constantTask answer : List Bool → List Bool)
    (hc : ∀ c, answer (clearedTask c) = S.toSource.value c)
    (hk : ∀ c, answer (constantTask c) = S.constantValue c) (c : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((program S clearedTask constantTask).controller.reference answer)^[t]
      ((program S clearedTask constantTask).initial c))).length ≤
        2 * c.length + 2 * (encNat 2).length + (BinaryNatCode.encode (S.modulus c)).length + 2 := by
  let : NeZero (S.modulus c) := ⟨S.modulus_ne_zero c⟩
  have HB (x : ZMod (S.modulus c)) : (residueBits x).length ≤ (BinaryNatCode.encode (S.modulus c)).length := by
    apply ModularFold.bits_length_le (fun _ => BinaryNatCode.encode (S.modulus c)) c x.val
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using ZMod.val_lt x
  have HC : (S.toSource.value c).length ≤ (BinaryNatCode.encode (S.modulus c)).length := by
    unfold IntegralClearedCoefficientBits.Source.value
    exact HB _
  have HO : (S.lowerValue c).length ≤ (BinaryNatCode.encode (S.modulus c)).length := by
    unfold Source.lowerValue
    exact HB _
  have H := TwoCall.state_length clearedTask constantTask (addPost S) answer c t
  rw [hc c, hk c, lower_value] at H
  exact H.trans (by omega)

end LeanCanny.Algebra.IntegralFrozenPowerBits.LowerStage

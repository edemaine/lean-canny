/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatFrozenSum
/-! # Guarded actual frozen constants on flat tasks -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatFrozenConstantBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks

noncomputable def program (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) :=
  IntegralFrozenPowerBits.ConstantStage.program S b (IntegralCriticalFlatEulerBits.next P .frozenPowerSum)

theorem controls (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralFrozenPowerBits.Source) (b : IntegralFrozenPowerBits.Access S) (hl : b.leading ∈ FP) :
    (program P S b).Controls :=
  IntegralFrozenPowerBits.ConstantStage.controls S b hl _ (IntegralCriticalFlatEulerBits.next_FP P a .frozenPowerSum)

theorem certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralFrozenPowerBits.Source) (b : IntegralFrozenPowerBits.Access S) (hl : b.leading ∈ FP) :
    (program P S b).controller.Certificates (encQ := encBits) (encS := SingleCall.encState) :=
  (program P S b).certificates (controls P a S b hl)

abbrev RepliesAt (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool) : Prop :=
  IntegralFrozenPowerBits.zeroTarget S c → answer (IntegralCriticalFlatEulerBits.next P .frozenPowerSum c) = S.sumValue c

theorem value_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) :
    (program P S b).value answer c = S.constantValue c := by
  rw [← IntegralFrozenPowerBits.constant_value S c]
  simp only [SingleCall.Program.value, program, IntegralFrozenPowerBits.ConstantStage.program, decide_eq_true_eq]
  by_cases hz : IntegralFrozenPowerBits.zeroTarget S c
  · rw [ite_eq_left hz, ite_eq_left hz, he hz]
    exact IntegralFrozenPowerBits.ConstantStage.finish_packet S b c
  · rw [ite_eq_right hz, ite_eq_right hz]

theorem halted_after (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) (answer : List Bool → List Bool) (c : List Bool) :
    (program P S b).controller.halted (((program P S b).controller.reference answer)^[1]
      (SingleCall.Program.initial c)) = true := (program P S b).halted_after answer c

theorem output_when_halted_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c)
    (t : ℕ) (hh : (program P S b).controller.halted (((program P S b).controller.reference answer)^[t]
      (SingleCall.Program.initial c)) = true) :
    (program P S b).controller.output (((program P S b).controller.reference answer)^[t]
      (SingleCall.Program.initial c)) = S.constantValue c :=
  ((program P S b).output_when_halted answer c t hh).trans (value_local P S b answer c he)

noncomputable def stateBound (S : IntegralFrozenPowerBits.Source) (c : List Bool) := 2 * c.length + 4 + (S.modulus c).size
theorem stateBound_unary (S : IntegralFrozenPowerBits.Source) (b : IntegralFrozenPowerBits.Access S) : UnaryFn (stateBound S) := by
  have HM : UnaryFn (fun c => (S.modulus c).size) :=
    (UnaryFn.length b.modulus.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 4)).add HM

theorem state_length_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) (t : ℕ) :
    (SingleCall.encState (((program P S b).controller.reference answer)^[t] (SingleCall.Program.initial c))).length ≤ stateBound S c := by
  apply (program P S b).state_length_of_bound answer c t (S.modulus c).size
  intro hr
  have hz : IntegralFrozenPowerBits.zeroTarget S c := of_decide_eq_true hr
  change (answer (IntegralCriticalFlatEulerBits.next P .frozenPowerSum c)).length ≤ _
  rw [he hz]
  let := S.ring c
  have : NeZero (S.modulus c) := ⟨S.modulus_ne_zero c⟩
  unfold IntegralFrozenPowerBits.Source.sumValue
  exact residueBits_length_le _ _

theorem requests_iff (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool) :
    (program P S b).controller.Requests answer budget c child ↔
      IntegralFrozenPowerBits.zeroTarget S c ∧ child = IntegralCriticalFlatEulerBits.next P .frozenPowerSum c :=
  IntegralFrozenPowerBits.ConstantStage.requests_iff S b _ answer budget c child

theorem requests_rank (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .frozenConstant c)
    (hc : (program P S b).controller.Requests answer budget c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨_, rfl⟩ := (requests_iff P S b answer budget c child).mp hc
  apply IntegralCriticalFlatEulerBits.next_lower_rank
  change IntegralCriticalHistoryTask.phase c = 11 at hp
  change 10 < IntegralCriticalHistoryTask.phase c
  omega

theorem requests_tasks (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (b : IntegralFrozenPowerBits.Access S) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (root c child : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P root c)
    (hc : (program P S b).controller.Requests answer budget c child) : IntegralCriticalHistoryTask.Tasks P root child := by
  obtain ⟨_, rfl⟩ := (requests_iff P S b answer budget c child).mp hc
  exact IntegralCriticalFlatEulerBits.next_tasks P .frozenPowerSum root c ht

end LeanCanny.Algebra.IntegralCriticalFlatFrozenConstantBits

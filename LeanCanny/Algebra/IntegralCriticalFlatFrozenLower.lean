/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatFrozenConstant
/-! # Actual flat frozen lower coefficients

The original cleared query explicitly selects expression 0. A second
fresh child supplies the frozen constant. Both replies retain the actual
old basis and are added by the native modular postprocessor.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatFrozenLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open IntegralCriticalFlatEulerRowsBits IntegralCriticalFlatEulerBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks

noncomputable def clearedTask (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source) (c : List Bool) :=
  spatial P .clearedGridSum 0 (pair c (pair (BinaryNatCode.encode (IntegralCriticalHistoryTask.get P .derivative c))
    (BinaryNatCode.encode (S.target c))))
theorem clearedTask_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralFrozenPowerBits.Source) (b : IntegralFrozenPowerBits.Access S) : clearedTask P S ∈ FP :=
  mem_FP_comp (f := fun c => pair c (pair (BinaryNatCode.encode (IntegralCriticalHistoryTask.get P .derivative c))
      (BinaryNatCode.encode (S.target c)))) (g := spatial P .clearedGridSum 0)
    (mem_FP_pair id_mem_FP (mem_FP_pair (IntegralCriticalHistoryTask.get_binary P a .derivative).bits_mem_FP b.target.bits_mem_FP))
    (spatial_FP P a .clearedGridSum 0)

theorem clearedTask_fields (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source) (c : List Bool)
    (ht : S.target c ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c)) :
    IntegralCriticalHistoryTask.get P .expression (clearedTask P S c) = 0 ∧
      IntegralCriticalHistoryTask.get P .target (clearedTask P S c) = S.target c ∧
      IntegralCriticalHistoryTask.get P .derivative (clearedTask P S c) = IntegralCriticalHistoryTask.get P .derivative c := by
  obtain ⟨hj, he, hx⟩ := spatial_fields P .clearedGridSum 0 c
    (IntegralCriticalHistoryTask.get P .derivative c) (S.target c)
    (IntegralCriticalHistoryTask.get_le P .derivative c) ht (Nat.zero_le _)
  exact ⟨hx, he, hj⟩

noncomputable def program (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source) :=
  IntegralFrozenPowerBits.LowerStage.program S (clearedTask P S) (next P .frozenConstant)

theorem certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralFrozenPowerBits.Source) (b : IntegralFrozenPowerBits.Access S) :
    (program P S).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  IntegralFrozenPowerBits.LowerStage.certificates S b _ _ (clearedTask_FP P a S b) (next_FP P a .frozenConstant)

theorem value_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool)
    (hc : answer (clearedTask P S c) = S.toSource.value c)
    (hk : answer (next P .frozenConstant c) = S.constantValue c) :
    (program P S).value answer c = S.lowerValue c := by
  change (TwoCall.program _ _ (IntegralFrozenPowerBits.addPost S)).value answer c = _
  rw [TwoCall.value_eq, hc, hk]
  exact IntegralFrozenPowerBits.lower_value S c

theorem halted_after (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool) :
    (program P S).controller.halted (((program P S).controller.reference answer)^[2] ((program P S).initial c)) = true :=
  (program P S).halted_after answer c

theorem output_when_halted_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool)
    (hc : answer (clearedTask P S c) = S.toSource.value c)
    (hk : answer (next P .frozenConstant c) = S.constantValue c) (t : ℕ)
    (hh : (program P S).controller.halted (((program P S).controller.reference answer)^[t] ((program P S).initial c)) = true) :
    (program P S).controller.output (((program P S).controller.reference answer)^[t] ((program P S).initial c)) = S.lowerValue c :=
  ((program P S).output_when_halted answer c t hh).trans (value_local P S answer c hc hk)

noncomputable def stateBound (S : IntegralFrozenPowerBits.Source) (c : List Bool) :=
  2 * c.length + 2 * (2 : ℕ).size + (S.modulus c).size + 2
theorem stateBound_unary (S : IntegralFrozenPowerBits.Source) (b : IntegralFrozenPowerBits.Access S) : UnaryFn (stateBound S) := by
  have HM : UnaryFn (fun c => (S.modulus c).size) :=
    (UnaryFn.length b.modulus.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const (2 * (2 : ℕ).size))).add HM).add (UnaryFn.const 2)

theorem state_length_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool)
    (hc : answer (clearedTask P S c) = S.toSource.value c)
    (hk : answer (next P .frozenConstant c) = S.constantValue c) (t : ℕ) :
    (RecursiveFold.encState (((program P S).controller.reference answer)^[t] ((program P S).initial c))).length ≤ stateBound S c := by
  let := S.ring c
  have : NeZero (S.modulus c) := ⟨S.modulus_ne_zero c⟩
  have HC : (S.toSource.value c).length ≤ (BinaryNatCode.encode (S.modulus c)).length := by
    unfold IntegralClearedCoefficientBits.Source.value
    rw [BinaryNatCode.length_encode]
    exact residueBits_length_le _ _
  have HL : (S.lowerValue c).length ≤ (BinaryNatCode.encode (S.modulus c)).length := by
    unfold IntegralFrozenPowerBits.Source.lowerValue
    rw [BinaryNatCode.length_encode]
    exact residueBits_length_le _ _
  have HP : IntegralFrozenPowerBits.addPost S (pair c (pair (S.toSource.value c) (S.constantValue c))) = S.lowerValue c :=
    IntegralFrozenPowerBits.lower_value S c
  have H := TwoCall.state_length (clearedTask P S) (next P .frozenConstant) (IntegralFrozenPowerBits.addPost S) answer c t
  rw [hc, hk, HP] at H
  have HB := H.trans (by omega : _ ≤ 2 * c.length + 2 * (encNat 2).length + (BinaryNatCode.encode (S.modulus c)).length + 2)
  simpa only [program, IntegralFrozenPowerBits.LowerStage.program, stateBound, encNat_apply,
    Nat.size_eq_bits_len, BinaryNatCode.length_encode] using HB

theorem requests_iff (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c child : List Bool) :
    (program P S).controller.Requests answer (fun _ => 2) c child ↔
      child = clearedTask P S c ∨ child = next P .frozenConstant c :=
  TwoCall.requests_iff _ _ _ answer c child

theorem requests_rank (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c child : List Bool) (hp : IntegralCriticalHistoryTask.isPhase .frozenLower c)
    (hc : (program P S).controller.Requests answer (fun _ => 2) c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  rcases (requests_iff P S answer c child).mp hc with rfl | rfl
  · have H := spatial_lower_rank P .clearedGridSum 0
      (pair c (pair (BinaryNatCode.encode (IntegralCriticalHistoryTask.get P .derivative c)) (BinaryNatCode.encode (S.target c))))
    simp only [pairFst_pair] at H
    apply H
    change IntegralCriticalHistoryTask.phase c = 12 at hp
    change 8 < IntegralCriticalHistoryTask.phase c
    omega
  · apply next_lower_rank
    change IntegralCriticalHistoryTask.phase c = 12 at hp
    change 11 < IntegralCriticalHistoryTask.phase c
    omega

theorem requests_tasks (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (root c child : List Bool) (ht : IntegralCriticalHistoryTask.Tasks P root c)
    (hc : (program P S).controller.Requests answer (fun _ => 2) c child) : IntegralCriticalHistoryTask.Tasks P root child := by
  rcases (requests_iff P S answer c child).mp hc with rfl | rfl
  · apply spatial_tasks
    simpa only [pairFst_pair] using ht
  · exact next_tasks P .frozenConstant root c ht

end LeanCanny.Algebra.IntegralCriticalFlatFrozenLowerBits

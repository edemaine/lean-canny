/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatFrozenTerm
/-! # Flat scans of actual frozen-height Fermat powers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatFrozenSumBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks

noncomputable def program (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source) :=
  IntegralFrozenPowerBits.SumStage.program S (IntegralCriticalFlatCoordinateQuery.writer P .frozenPowerTerm)

theorem certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralFrozenPowerBits.Source) (b : IntegralFrozenPowerBits.Access S) :
    (program P S).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  IntegralFrozenPowerBits.SumStage.certificates S b _ (IntegralCriticalFlatCoordinateQuery.writer_FP P a .frozenPowerTerm)

abbrev RepliesAt (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool) : Prop :=
  ∀ i < S.arity c, answer (IntegralCriticalFlatCoordinateQuery.writer P .frozenPowerTerm
    (pair c (BinaryNatCode.encode i))) = IntegralFrozenPowerBits.termProgram S (pair c (BinaryNatCode.encode i))

theorem partial_value_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) (k : ℕ) (hk : k ≤ S.arity c) :
    (program P S).partialValue answer c k = residueBits (∑ i ∈ Finset.range k, (S.summand c i : ZMod (S.modulus c))) :=
  ModularFold.RecursiveStage.sum_partialValueWithModulus S.arity (fun c => BinaryNatCode.encode (S.modulus c))
    (IntegralCriticalFlatCoordinateQuery.writer P .frozenPowerTerm) answer S.modulus
    (funext (fun _ => Nat.fromBitsLE_bits _)) c (fun i => (S.summand c i : ZMod (S.modulus c)))
    (Nat.pos_of_ne_zero (S.modulus_ne_zero c))
    (fun i hi => (he i hi).trans (IntegralFrozenPowerBits.term_packet S c i)) k hk

theorem value_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) :
    (program P S).value answer c = S.sumValue c :=
  (partial_value_local P S answer c he _ le_rfl).trans (IntegralFrozenPowerBits.sum_value S c)

theorem halted_after (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool) :
    (program P S).controller.halted (((program P S).controller.reference answer)^[S.arity c]
      ((program P S).initial c)) = true := (program P S).halted_after answer c

theorem output_when_halted_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) (t : ℕ)
    (hh : (program P S).controller.halted (((program P S).controller.reference answer)^[t]
      ((program P S).initial c)) = true) :
    (program P S).controller.output (((program P S).controller.reference answer)^[t] ((program P S).initial c)) = S.sumValue c :=
  ((program P S).output_when_halted answer c t hh).trans (value_local P S answer c he)

noncomputable def stateBound (S : IntegralFrozenPowerBits.Source) (c : List Bool) : ℕ :=
  2 * c.length + 2 * (S.arity c).size + (S.modulus c).size + 2

theorem stateBound_unary (S : IntegralFrozenPowerBits.Source) (b : IntegralFrozenPowerBits.Access S) : UnaryFn (stateBound S) := by
  have HA : UnaryFn (fun c => (S.arity c).size) :=
    (UnaryFn.length (BinaryFn.ofUnary b.arity).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  have HM : UnaryFn (fun c => (S.modulus c).size) :=
    (UnaryFn.length b.modulus.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul HA)).add HM).add (UnaryFn.const 2)

theorem state_length_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) (t : ℕ) :
    (RecursiveFold.encState (((program P S).controller.reference answer)^[t] ((program P S).initial c))).length ≤ stateBound S c := by
  have H : (RecursiveFold.encState (((program P S).controller.reference answer)^[t] ((program P S).initial c))).length ≤
      2 * c.length + 2 * (encNat (S.arity c)).length + (BinaryNatCode.encode (S.modulus c)).length + 2 := by
    apply (program P S).orbit_length
    intro k hk
    rw [partial_value_local P S answer c he k hk]
    have : NeZero (S.modulus c) := ⟨S.modulus_ne_zero c⟩
    apply ModularFold.bits_length_le (fun c => BinaryNatCode.encode (S.modulus c)) c
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using
      ZMod.val_lt (∑ i ∈ Finset.range k, (S.summand c i : ZMod (S.modulus c)))
  simpa only [stateBound, encNat_apply, Nat.size_eq_bits_len, BinaryNatCode.length_encode] using H

theorem requests_iff (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c child : List Bool) :
    (program P S).controller.Requests answer S.arity c child ↔
      ∃ i < S.arity c, child = IntegralCriticalFlatCoordinateQuery.writer P .frozenPowerTerm (pair c (BinaryNatCode.encode i)) :=
  IntegralFrozenPowerBits.SumStage.requests_iff S _ answer c child

theorem requests_rank (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (c child : List Bool) (hp : IntegralCriticalHistoryTask.isPhase .frozenPowerSum c)
    (hc : (program P S).controller.Requests answer S.arity c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨i, _, rfl⟩ := (requests_iff P S answer c child).mp hc
  have H := IntegralCriticalFlatCoordinateQuery.writer_lower_rank P .frozenPowerTerm (pair c (BinaryNatCode.encode i))
  simp only [pairFst_pair] at H
  apply H
  change IntegralCriticalHistoryTask.phase c = 10 at hp
  change 9 < IntegralCriticalHistoryTask.phase c
  omega

theorem requests_tasks (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralFrozenPowerBits.Source)
    (answer : List Bool → List Bool) (root c child : List Bool) (ht : IntegralCriticalHistoryTask.Tasks P root c)
    (hc : (program P S).controller.Requests answer S.arity c child) : IntegralCriticalHistoryTask.Tasks P root child := by
  obtain ⟨i, _, rfl⟩ := (requests_iff P S answer c child).mp hc
  apply IntegralCriticalFlatCoordinateQuery.writer_tasks
  simpa only [pairFst_pair] using ht

end LeanCanny.Algebra.IntegralCriticalFlatFrozenSumBits

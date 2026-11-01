/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegerZeroSpace
public import LeanCanny.Computation.RecursiveFoldController
/-! # Resumable integer zero tests from charged small-modulus residues

The scan stores a binary counter and a single Boolean. Each residue is a
recursive request; its evaluator is not a local certificate premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegerZeroBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def count (budget : List Bool → ℕ) (q : List Bool) : ℕ := 2 * budget q + 4

def finish (z : List Bool) : List Bool :=
  [decide (BoundedFold.accumulator (pairFst z) = [true] ∧ pairSnd z = [])]

theorem finish_FP : finish ∈ FP :=
  ((stringEq_fppred (mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP) (constFn_mem_FP [true])).and
    (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP []))).flag_mem_FP

def program (budget : List Bool → ℕ) (task : List Bool → List Bool) : RecursiveFold.Program where
  count := count budget
  seed _ := [true]
  entryTask := task
  finish := finish

theorem certificates (budget : List Bool → ℕ) (hb : BinaryFn budget) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (program budget task).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  RecursiveFold.Program.certificates _ (((BinaryFn.const 2).mul hb).add (BinaryFn.const 4))
    (constFn_mem_FP [true]) ht finish_FP

theorem partialValue (budget : List Bool → ℕ) (task answer : List Bool → List Bool) (q : List Bool) (k : ℕ) :
    (program budget task).partialValue answer q k =
      [decide (∀ i < k, answer (task (pair q (BinaryNatCode.encode i))) = [])] := by
  induction k with
  | zero => simp [RecursiveFold.Program.partialValue, BoundedFold.fold, program]
  | succ k ih =>
    change (program budget task).update answer
      (BoundedFold.packet q k ((program budget task).partialValue answer q k)) = _
    rw [ih]
    simp only [RecursiveFold.Program.update, BoundedFold.update, program, finish, Function.comp_apply,
      BoundedFold.query, BoundedFold.context_packet, BoundedFold.counter_packet, pairFst_pair, pairSnd_pair,
      BoundedFold.accumulator_packet, List.cons.injEq, and_true, decide_eq_true_eq]
    congr 2
    apply propext
    constructor
    · rintro ⟨h, hk⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hk
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h k (Nat.lt_succ_self k)⟩

theorem value_at (budget : List Bool → ℕ) (task answer : List Bool → List Bool) (q : List Bool) (z : ℤ)
    (hb : z.natAbs.size ≤ budget q)
    (hr : ∀ i < count budget q, answer (task (pair q (BinaryNatCode.encode i))) = residueBits (z : ZMod (i + 1))) :
    (program budget task).value answer q = [decide (z = 0)] := by
  rw [RecursiveFold.Program.value, partialValue]
  have HE : (∀ i < count budget q, answer (task (pair q (BinaryNatCode.encode i))) = []) ↔ z = 0 := by
    rw [IntegerModular.eq_zero_iff_residues z (budget q) hb]
    constructor
    · intro h m hm hl
      have HI : m - 1 < count budget q := by unfold count; omega
      have H := (hr (m - 1) HI).symm.trans (h (m - 1) HI)
      have HM : m - 1 + 1 = m := by omega
      rw [HM] at H
      let : NeZero m := ⟨by omega⟩
      exact (residueBits_injective m) (H.trans (ArithmeticBits.zero_residueBits m))
    · intro h i hi
      rw [hr i hi, h (i + 1) (by omega) (by unfold count at hi; omega)]
      exact (ArithmeticBits.zero_residueBits (i + 1)).symm
  simp only [program, HE]

theorem requests_cases (budget : List Bool → ℕ) (task answer : List Bool → List Bool)
    (steps : List Bool → ℕ) (q c : List Bool)
    (hc : (program budget task).controller.Requests answer steps q c) :
    ∃ i < count budget q, c = task (pair q (BinaryNatCode.encode i)) := by
  let P := program budget task
  obtain ⟨t, _, hh, _, he⟩ := hc
  have HI : min t (P.count q) < P.count q := by
    rw [show P.controller.initial q = P.initial q from rfl, P.reference_iterate] at hh
    have H : ¬ P.count q ≤ min t (P.count q) := of_decide_eq_false hh
    omega
  refine ⟨min t (P.count q), HI, ?_⟩
  rw [show P.controller.initial q = P.initial q from rfl, P.reference_iterate] at he
  exact he

def stateBound (budget : List Bool → ℕ) (q : List Bool) : ℕ :=
  2 * q.length + 2 * (encNat (count budget q)).length + 3

theorem stateBound_unary (budget : List Bool → ℕ) (hb : BinaryFn budget) : UnaryFn (stateBound budget) := by
  have HC : BinaryFn (count budget) := ((BinaryFn.const 2).mul hb).add (BinaryFn.const 4)
  have HL : UnaryFn (fun q => (encNat (count budget q)).length) :=
    (UnaryFn.length HC.bits_mem_FP).of_eq (fun q => by
      simp only [length_encNat_eq_size, Nat.size_eq_bits_len, BinaryNatCode.encode])
  exact (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul HL)).add (UnaryFn.const 3)

theorem state_length (budget : List Bool → ℕ) (task answer : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((program budget task).controller.reference answer)^[t]
      ((program budget task).initial q))).length ≤ stateBound budget q := by
  have H := (program budget task).orbit_length answer q t 1 (fun i _ => by rw [partialValue]; rfl)
  exact H

end LeanCanny.Algebra.IntegerZeroBits.RecursiveStage

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.RecursiveFoldController

/-! # Two recursive replies followed by local FP processing

A two-step fold retains the original context and the first reply. The
second resume replaces that reply by the locally processed result. No
child evaluator or child execution clock is used by the certificate.
-/

@[expose] public section
namespace LeanCanny.Computation.TwoCall
open LeanCanny.Encoding Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

def entryTask (left right : List Bool → List Bool) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd q) = 0 then left (pairFst q) else right (pairFst q)

def finish (post : List Bool → List Bool) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (BoundedFold.counter (pairFst z)) = 0 then pairSnd z else
    post (pair (pairFst (pairFst z)) (pair (BoundedFold.accumulator (pairFst z)) (pairSnd z)))

def program (left right post : List Bool → List Bool) : RecursiveFold.Program where
  count _ := 2
  seed _ := []
  entryTask := entryTask left right
  finish := finish post

theorem entryTask_FP (left right : List Bool → List Bool) (hl : left ∈ FP) (hr : right ∈ FP) : entryTask left right ∈ FP :=
  ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)).ite_mem_FP
    (mem_FP_comp (f := pairFst) (g := left) pairFst_mem_FP hl)
    (mem_FP_comp (f := pairFst) (g := right) pairFst_mem_FP hr)

theorem finish_FP (post : List Bool → List Bool) (hp : post ∈ FP) : finish post ∈ FP := by
  have HC : BinaryFn (fun z => Nat.fromBitsLE (BoundedFold.counter (pairFst z))) := by
    have H : BinaryFn (fun p => Nat.fromBitsLE (BoundedFold.counter p)) := BinaryFn.fromBits BoundedFold.counter_mem_FP
    exact H.comp pairFst_mem_FP
  have HQ : (fun z => pairFst (pairFst z)) ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HA : (fun z => BoundedFold.accumulator (pairFst z)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := BoundedFold.accumulator) pairFst_mem_FP BoundedFold.accumulator_mem_FP
  have H := mem_FP_comp (mem_FP_pair HQ (mem_FP_pair HA pairSnd_mem_FP)) hp
  exact (HC.eq (BinaryFn.const 0)).ite_mem_FP pairSnd_mem_FP H

theorem certificates (left right post : List Bool → List Bool) (hl : left ∈ FP) (hr : right ∈ FP) (hp : post ∈ FP) :
    (program left right post).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  RecursiveFold.Program.certificates _ (BinaryFn.const 2) (constFn_mem_FP []) (entryTask_FP left right hl hr) (finish_FP post hp)

theorem update_packet (left right post answer : List Bool → List Bool) (q : List Bool) (i : ℕ) (v : List Bool) :
    (program left right post).update answer (BoundedFold.packet q i v) =
      if i = 0 then answer (left q) else post (pair q (pair v (answer (right q)))) := by
  simp only [RecursiveFold.Program.update, BoundedFold.update, program, finish, entryTask,
    BoundedFold.query, BoundedFold.context_packet, BoundedFold.counter_packet, Function.comp_apply,
    pairFst_pair, pairSnd_pair, BoundedFold.accumulator_packet, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs <;> rfl

theorem partial_one (left right post answer : List Bool → List Bool) (q : List Bool) :
    (program left right post).partialValue answer q 1 = answer (left q) := by
  change (program left right post).update answer (BoundedFold.packet q 0 []) = _
  rw [update_packet, ite_eq_left rfl]

theorem partial_two (left right post answer : List Bool → List Bool) (q : List Bool) :
    (program left right post).partialValue answer q 2 = post (pair q (pair (answer (left q)) (answer (right q)))) := by
  change (program left right post).update answer
    (BoundedFold.packet q 1 ((program left right post).partialValue answer q 1)) = _
  rw [partial_one, update_packet, ite_eq_right (by decide : ¬(1 : ℕ) = 0)]

theorem value_eq (left right post answer : List Bool → List Bool) (q : List Bool) :
    (program left right post).value answer q = post (pair q (pair (answer (left q)) (answer (right q)))) :=
  partial_two left right post answer q

theorem state_length (left right post answer : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((program left right post).controller.reference answer)^[t]
      ((program left right post).initial q))).length ≤
        2 * q.length + 2 * (encNat 2).length +
        max (answer (left q)).length (post (pair q (pair (answer (left q)) (answer (right q))))).length + 2 := by
  apply RecursiveFold.Program.orbit_length
  intro i hi
  change i ≤ 2 at hi
  have HI : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases HI with rfl | rfl | rfl
  · exact Nat.zero_le _
  · rw [partial_one]; exact Nat.le_max_left _ _
  · rw [partial_two]; exact Nat.le_max_right _ _

theorem halted_after (left right post answer : List Bool → List Bool) (q : List Bool) :
    (program left right post).controller.halted
      (((program left right post).controller.reference answer)^[2] ((program left right post).initial q)) = true :=
  (program left right post).halted_after answer q

theorem output_when_halted (left right post answer : List Bool → List Bool) (q : List Bool) (t : ℕ)
    (hh : (program left right post).controller.halted
      (((program left right post).controller.reference answer)^[t] ((program left right post).initial q)) = true) :
    (program left right post).controller.output
      (((program left right post).controller.reference answer)^[t] ((program left right post).initial q)) =
        post (pair q (pair (answer (left q)) (answer (right q)))) :=
  ((program left right post).output_when_halted answer q t hh).trans (value_eq left right post answer q)

theorem requests_iff (left right post answer : List Bool → List Bool) (q child : List Bool) :
    (program left right post).controller.Requests answer (fun _ => 2) q child ↔ child = left q ∨ child = right q := by
  change (program left right post).controller.Requests answer (program left right post).count q child ↔ _
  rw [(program left right post).requests_iff answer q child]
  simp only [RecursiveFold.Program.child, program, entryTask, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  constructor
  · rintro ⟨i, hi, he⟩
    have HI : i = 0 ∨ i = 1 := by omega
    rcases HI with rfl | rfl
    · exact Or.inl (by simpa only [ite_true] using he)
    · exact Or.inr (by simpa only [show ¬(1 : ℕ) = 0 from by decide, ite_false] using he)
  · rintro (he | he)
    · exact ⟨0, by decide, by simpa only [ite_true] using he⟩
    · exact ⟨1, by decide, by simpa only [show ¬(1 : ℕ) = 0 from by decide, ite_false] using he⟩

end LeanCanny.Computation.TwoCall

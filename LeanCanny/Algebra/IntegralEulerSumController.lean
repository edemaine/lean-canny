/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralEulerTermSpace
public import LeanCanny.Algebra.ModularFoldRecursiveController
public import LeanCanny.Computation.ControllerRequests

/-! # Resumable Euler sums and their coordinate-term requests

A modular fold scans the original free coordinates. Its term selector
returns zero locally at the objective coordinate and otherwise requests
one coordinate-times-gradient coefficient. Only metadata and task writers
are used by the native certificates.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralEulerBits.SumStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

noncomputable def term (S : Source) (task : List Bool → List Bool) : SingleCall.Program where
  request p := !(decide (excluded S p))
  query p := task (termQuery S p)
  immediate _ := []
  finish := pairSnd

theorem term_controls (S : Source) (a : Access S) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (term S task).Controls := by
  have H := (excluded_fppred S a).not.flag_mem_FP
  refine ⟨?_, ?_, constFn_mem_FP [], pairSnd_mem_FP⟩
  · change (fun p => [!decide (excluded S p)]) ∈ FP
    exact mem_FP_of_eq H (fun _ => by simp only [decide_not])
  · exact mem_FP_comp (f := termQuery S) (g := task) (termQuery_FP S a) ht

attribute [local irreducible] IntegralCriticalCoordinateProductBits.value termProgram Source.sumValue

theorem term_value (S : Source) (task answer : List Bool → List Bool)
    (he : ∀ p, answer (task p) = IntegralCriticalCoordinateProductBits.value S.toGradient p) (p : List Bool) :
    (term S task).value answer p = termProgram S p := by
  by_cases h : excluded S p <;>
    simp only [SingleCall.Program.value, term, h, decide_true, decide_false, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ite_true, ite_false, pairSnd_pair, termProgram, he]

theorem term_requests_iff (S : Source) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (p child : List Bool) :
    (term S task).controller.Requests answer budget p child ↔ ¬excluded S p ∧ child = task (termQuery S p) := by
  rw [SingleCall.Program.requests_iff]
  simp only [term, Bool.not_eq_true', decide_eq_false_iff_not]

noncomputable def program (S : Source) (task : List Bool → List Bool) : RecursiveFold.Program :=
  ModularFold.RecursiveStage.sumProgram S.free (fun c => BinaryNatCode.encode (S.modulus c)) task

theorem certificates (S : Source) (a : Access S) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (program S task).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  ModularFold.RecursiveStage.sum_certificates _ _ task (BinaryFn.ofUnary a.free) a.modulus.bits_mem_FP ht

theorem partial_value (S : Source) (task answer : List Bool → List Bool)
    (he : ∀ p, answer (task p) = termProgram S p) (c : List Bool) (k : ℕ) (hk : k ≤ S.free c) :
    (program S task).partialValue answer c k = residueBits (∑ i ∈ Finset.range k, (S.summand c i : ZMod (S.modulus c))) := by
  exact ModularFold.RecursiveStage.sum_partialValueWithModulus S.free
    (fun c => BinaryNatCode.encode (S.modulus c)) task answer S.modulus
    (funext fun c => Nat.fromBitsLE_bits _) c (fun i => (S.summand c i : ZMod (S.modulus c)))
    (Nat.pos_of_ne_zero (S.modulus_ne_zero c))
    (fun i hi => (he _).trans (term_packet S c ⟨i, hi⟩)) k hk

theorem value_eq (S : Source) (task answer : List Bool → List Bool)
    (he : ∀ p, answer (task p) = termProgram S p) (c : List Bool) :
    (program S task).value answer c = S.sumValue c :=
  (partial_value S task answer he c _ le_rfl).trans (sum_value S c)

theorem halted_after (S : Source) (task answer : List Bool → List Bool) (c : List Bool) :
    (program S task).controller.halted
      (((program S task).controller.reference answer)^[S.free c] ((program S task).initial c)) = true :=
  (program S task).halted_after answer c

theorem output_when_halted (S : Source) (task answer : List Bool → List Bool)
    (he : ∀ p, answer (task p) = termProgram S p) (c : List Bool) (t : ℕ)
    (hh : (program S task).controller.halted
      (((program S task).controller.reference answer)^[t] ((program S task).initial c)) = true) :
    (program S task).controller.output
      (((program S task).controller.reference answer)^[t] ((program S task).initial c)) = S.sumValue c :=
  ((program S task).output_when_halted answer c t hh).trans (value_eq S task answer he c)

theorem state_length (S : Source) (task answer : List Bool → List Bool)
    (he : ∀ p, answer (task p) = termProgram S p) (c : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((program S task).controller.reference answer)^[t] ((program S task).initial c))).length ≤
      2 * c.length + 2 * (encNat (S.free c)).length + (BinaryNatCode.encode (S.modulus c)).length + 2 := by
  apply RecursiveFold.Program.orbit_length
  intro k hk
  rw [partial_value S task answer he c k hk]
  let : NeZero (S.modulus c) := ⟨S.modulus_ne_zero c⟩
  apply ModularFold.bits_length_le (fun c => BinaryNatCode.encode (S.modulus c)) c
  have HD (m : ℕ) : Nat.fromBitsLE (BinaryNatCode.encode m) = m := Nat.fromBitsLE_bits m
  simpa only [HD] using
    ZMod.val_lt (∑ i ∈ Finset.range k, (S.summand c i : ZMod (S.modulus c)))

theorem requests_iff (S : Source) (task answer : List Bool → List Bool) (c child : List Bool) :
    (program S task).controller.Requests answer S.free c child ↔
      ∃ i < S.free c, child = task (pair c (BinaryNatCode.encode i)) := by
  change (program S task).controller.Requests answer (program S task).count c child ↔ _
  exact (program S task).requests_iff answer c child

end LeanCanny.Algebra.IntegralEulerBits.SumStage

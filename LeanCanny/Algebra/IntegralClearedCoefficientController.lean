/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralClearedCoefficientSpace
public import LeanCanny.Algebra.ModularFoldRecursiveController
public import LeanCanny.Computation.ControllerRequests

/-! # Recursive original-grid sums for frozen substitution

A local mask discards incompatible free exponents. The outer modular fold
streams the original spatial grid and requests one compatible term at a
time. The old algebra rank remains separate from this spatial grid.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralClearedCoefficientBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def term (S : Source) (task : List Bool → List Bool) : SingleCall.Program where
  request p := decide (ClearedCoordinateExponentBits.mask (maskLayout S) p)
  query := task
  immediate _ := []
  finish := pairSnd

theorem term_controls (S : Source) (a : Access S) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (term S task).Controls :=
  ⟨(ClearedCoordinateExponentBits.mask_fppred (maskLayout S) (mask_controls S a)).flag_mem_FP,
    ht, constFn_mem_FP [], pairSnd_mem_FP⟩

attribute [local irreducible] IntegralMonomialTermBits.Source.value maskedProgram Source.value

theorem term_value (S : Source) (task answer : List Bool → List Bool)
    (he : ∀ p, answer (task p) = (termSource S).value p) (p : List Bool) :
    (term S task).value answer p = maskedProgram S p := by
  simp only [SingleCall.Program.value, term, decide_eq_true_eq, pairSnd_pair, he, maskedProgram]

theorem term_requests_iff (S : Source) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (p child : List Bool) :
    (term S task).controller.Requests answer budget p child ↔
      ClearedCoordinateExponentBits.mask (maskLayout S) p ∧ child = task p := by
  rw [SingleCall.Program.requests_iff]
  simp only [term, decide_eq_true_eq]

def count (S : Source) (c : List Bool) := FixedWidthPolynomial.count (S.arity c) (S.sourceWidth c)

theorem count_binary (S : Source) (a : Access S) : BinaryFn (count S) :=
  (BinaryFn.fromBits (FixedWidthPolynomial.countCode_mem_FP a.arity a.sourceWidth)).of_eq
    (fun c => by rw [FixedWidthPolynomial.countCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)

noncomputable def program (S : Source) (task : List Bool → List Bool) : RecursiveFold.Program :=
  ModularFold.RecursiveStage.sumProgram (count S) (fun c => BinaryNatCode.encode (S.modulus c)) task

theorem certificates (S : Source) (a : Access S) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (program S task).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  ModularFold.RecursiveStage.sum_certificates _ _ task (count_binary S a) a.modulus.bits_mem_FP ht

theorem partial_value (S : Source) (task answer : List Bool → List Bool)
    (he : ∀ p, answer (task p) = maskedProgram S p) (c : List Bool) (k : ℕ) (hk : k ≤ count S c) :
    (program S task).partialValue answer c k = residueBits (∑ i ∈ Finset.range k, (S.summand c i : ZMod (S.modulus c))) :=
  ModularFold.RecursiveStage.sum_partialValueWithModulus (count S)
    (fun c => BinaryNatCode.encode (S.modulus c)) task answer S.modulus
    (funext fun _ => Nat.fromBitsLE_bits _) c (fun i => (S.summand c i : ZMod (S.modulus c)))
    (Nat.pos_of_ne_zero (S.modulus_ne_zero c))
    (fun i hi => (he _).trans (masked_packet S c i hi)) k hk

theorem value_eq (S : Source) (task answer : List Bool → List Bool)
    (he : ∀ p, answer (task p) = maskedProgram S p) (c : List Bool) :
    (program S task).value answer c = S.value c :=
  (partial_value S task answer he c _ le_rfl).trans (sum_value S c)

theorem halted_after (S : Source) (task answer : List Bool → List Bool) (c : List Bool) :
    (program S task).controller.halted
      (((program S task).controller.reference answer)^[count S c] ((program S task).initial c)) = true :=
  (program S task).halted_after answer c

theorem output_when_halted (S : Source) (task answer : List Bool → List Bool)
    (he : ∀ p, answer (task p) = maskedProgram S p) (c : List Bool) (t : ℕ)
    (hh : (program S task).controller.halted
      (((program S task).controller.reference answer)^[t] ((program S task).initial c)) = true) :
    (program S task).controller.output
      (((program S task).controller.reference answer)^[t] ((program S task).initial c)) = S.value c :=
  ((program S task).output_when_halted answer c t hh).trans (value_eq S task answer he c)

theorem state_length (S : Source) (task answer : List Bool → List Bool)
    (he : ∀ p, answer (task p) = maskedProgram S p) (c : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((program S task).controller.reference answer)^[t] ((program S task).initial c))).length ≤
      2 * c.length + 2 * (encNat (count S c)).length + (BinaryNatCode.encode (S.modulus c)).length + 2 := by
  apply RecursiveFold.Program.orbit_length
  intro k hk
  rw [partial_value S task answer he c k hk]
  let : NeZero (S.modulus c) := ⟨S.modulus_ne_zero c⟩
  apply ModularFold.bits_length_le (fun c => BinaryNatCode.encode (S.modulus c)) c
  simpa only [show Nat.fromBitsLE (BinaryNatCode.encode (S.modulus c)) = S.modulus c from Nat.fromBitsLE_bits _] using
    ZMod.val_lt (∑ i ∈ Finset.range k, (S.summand c i : ZMod (S.modulus c)))

theorem requests_iff (S : Source) (task answer : List Bool → List Bool) (c child : List Bool) :
    (program S task).controller.Requests answer (count S) c child ↔
      ∃ i < count S c, child = task (pair c (BinaryNatCode.encode i)) :=
  (program S task).requests_iff answer c child

end LeanCanny.Algebra.IntegralClearedCoefficientBits.RecursiveStage

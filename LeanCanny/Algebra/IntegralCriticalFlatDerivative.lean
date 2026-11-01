/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatDerivativeQuery

/-! # Guarded actual derivative coefficients on flat tasks

The source may be any actual Euler source, including the total creating
source. Its selected spatial derivative bumps one original exponent and
multiplies the requested coefficient by the native incremented exponent.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralDerivativeBits
open LeanCanny.Encoding LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

noncomputable def flatRequest (S : Source) (z : List Bool) : Prop :=
  FixedWidthQuery.Bounded (arity S) (width S) pairSnd (fun z => degree S z - 1) z

noncomputable def flatQuery (S : Source) (z : List Bool) : List Bool :=
  coefficientQuery (FixedWidthDerivativeBits.query (arity S) (width S) (width S) (selected S) pairSnd z)

theorem flatQuery_original (S : Source) (z : List Bool) : original (flatQuery S z) = original z := by
  simp only [flatQuery, coefficientQuery, FixedWidthDerivativeBits.query, original, pairFst_pair]

theorem program_value_at (S : Source) (a : Access S) (task answer : List Bool → List Bool) (z : List Bool)
    (he : flatRequest S z → answer (task (flatQuery S z)) = a.coefficient (flatQuery S z)) :
    (program S task).value answer z = value S a z := by
  classical
  unfold program value FixedWidthDerivativeBits.program FixedWidthDerivativeBits.value
  simp only [SingleCall.Program.value, decide_eq_true_eq, Function.comp_apply]
  change (if flatRequest S z then _ else []) = (if flatRequest S z then _ else [])
  by_cases hb : flatRequest S z
  · rw [ite_eq_left hb, ite_eq_left hb]
    simpa only [flatQuery] using congrArg
      (fun reply => FixedWidthDerivativeBits.finish (arity S) (width S) (selected S) pairSnd (modulus S) (pair z reply)) (he hb)
  · rw [ite_eq_right hb, ite_eq_right hb]

end LeanCanny.Algebra.IntegralDerivativeBits

namespace LeanCanny.Algebra.IntegralCriticalFlatDerivativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks
attribute [local irreducible] IntegralCriticalFlatDerivativeQuery.writer

variable (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralDerivativeBits.Source) (b : IntegralDerivativeBits.Access S)

noncomputable def input := IntegralCriticalFlatOriginalCoefficientBits.packet P S.toSource

include a b in
theorem input_FP : input P S ∈ FP :=
  IntegralCriticalFlatOriginalCoefficientBits.packet_FP P a S.toSource b.toAccess

theorem input_original (c : List Bool) : IntegralDerivativeBits.original (input P S c) = c := by
  simp only [input, IntegralCriticalFlatOriginalCoefficientBits.packet, IntegralDerivativeBits.original,
    IntegralClearedCoefficientBits.context, pairFst_pair]

noncomputable def program : SingleCall.Program :=
  IntegralDerivativeBits.program S (IntegralCriticalFlatDerivativeQuery.writer P)
noncomputable def controller := (program P S).controller.prepare (input P S)

include a b in
theorem controls : (program P S).Controls :=
  IntegralDerivativeBits.program_controls S b _ (IntegralCriticalFlatDerivativeQuery.writer_FP P a)

include a b in
theorem certificates : (controller P S).Certificates (encQ := encBits) (encS := SingleCall.encState) :=
  (program P S).controller.prepare_certificates _ ((program P S).certificates (controls P a S b)) (input_FP P a S b)

abbrev Replies (answer : List Bool → List Bool) : Prop :=
  ∀ c, IntegralDerivativeBits.flatRequest S (input P S c) →
    answer (IntegralCriticalFlatDerivativeQuery.writer P (IntegralDerivativeBits.flatQuery S (input P S c))) =
      b.coefficient (IntegralDerivativeBits.flatQuery S (input P S c))

theorem value (answer : List Bool → List Bool) (he : Replies P S b answer) (c : List Bool) :
    letI := S.ring c
    (program P S).value answer (input P S c) = residueBits
      ((Algebra.leftMulMatrix (S.basis c) ((MvPolynomial.pderiv (S.selected c) (S.polynomial c)).coeff
        (RationalSubstitution.Indexed.exponentVector (S.arity c) (FixedWidthPolynomial.entry (S.sourceWidth c)
          (IntegralCriticalHistoryTask.get P .sourceIndex c))))
        (IntegralCriticalFlatOriginalCoefficientBits.index P S.toSource .row c)
        (IntegralCriticalFlatOriginalCoefficientBits.index P S.toSource .col c) : ℤ) : ZMod (S.modulus c)) :=
  (IntegralDerivativeBits.program_value_at S b (IntegralCriticalFlatDerivativeQuery.writer P) answer
    (input P S c) (he c)).trans (IntegralDerivativeBits.packet S b c _
      (IntegralCriticalFlatOriginalCoefficientBits.index P S.toSource .row c)
      (IntegralCriticalFlatOriginalCoefficientBits.index P S.toSource .col c))

theorem halted_after (answer : List Bool → List Bool) (c : List Bool) :
    (controller P S).halted (((controller P S).reference answer)^[1] ((controller P S).initial c)) = true := by
  simpa only [controller, RecursiveController.Controller.prepare_halted_iterate, SingleCall.Program.controller] using
    (program P S).halted_after answer (input P S c)

theorem output_when_halted (answer : List Bool → List Bool) (he : Replies P S b answer) (c : List Bool) (t : ℕ)
    (hh : (controller P S).halted (((controller P S).reference answer)^[t] ((controller P S).initial c)) = true) :
    (controller P S).output (((controller P S).reference answer)^[t] ((controller P S).initial c)) =
      IntegralDerivativeBits.value S b (input P S c) := by
  simp only [controller, RecursiveController.Controller.prepare_halted_iterate, SingleCall.Program.controller] at hh
  simpa only [controller, RecursiveController.Controller.prepare_output_iterate, SingleCall.Program.controller] using
    ((program P S).output_when_halted answer (input P S c) t hh).trans
      (IntegralDerivativeBits.program_value_at S b (IntegralCriticalFlatDerivativeQuery.writer P) answer _ (he c))

noncomputable def bumpedIndex (c : List Bool) : ℕ :=
  Nat.fromBitsLE (FixedWidthDerivativeBits.packed (IntegralDerivativeBits.arity S) (IntegralDerivativeBits.width S)
    (IntegralDerivativeBits.width S) (IntegralDerivativeBits.selected S) pairSnd (input P S c))

private theorem wordValue_lt (w : List Bool) : Nat.fromBitsLE w < 2 ^ w.length := by
  induction w with
  | nil => decide
  | cons bit bits ih =>
    rw [Nat.fromBitsLE_cons, List.length_cons, Nat.pow_succ]
    split_ifs <;> omega

theorem bumpedIndex_lt (c : List Bool) :
    bumpedIndex P S c < FixedWidthPolynomial.count (S.arity c) (S.sourceWidth c) := by
  have H := wordValue_lt (FixedWidthDerivativeBits.packed (IntegralDerivativeBits.arity S) (IntegralDerivativeBits.width S)
    (IntegralDerivativeBits.width S) (IntegralDerivativeBits.selected S) pairSnd (input P S c))
  simp only [FixedWidthDerivativeBits.packed, FixedWidthNatVector.length_encode, IntegralDerivativeBits.arity,
    IntegralDerivativeBits.width, input_original] at H
  simpa only [bumpedIndex, FixedWidthDerivativeBits.packed, IntegralDerivativeBits.arity,
    IntegralDerivativeBits.width, input_original, FixedWidthPolynomial.count, ← Nat.pow_mul, Nat.mul_comm] using H

theorem query_packet (c : List Bool) :
    IntegralDerivativeBits.flatQuery S (input P S c) =
      pair (IntegralClearedCoefficientBits.context c
        (IntegralCriticalFlatOriginalCoefficientBits.index P S.toSource .row c).val
        (IntegralCriticalFlatOriginalCoefficientBits.index P S.toSource .col c).val)
        (BinaryNatCode.encode (bumpedIndex P S c)) := by
  simp only [IntegralDerivativeBits.flatQuery, IntegralDerivativeBits.coefficientQuery,
    FixedWidthDerivativeBits.query, input, IntegralCriticalFlatOriginalCoefficientBits.packet,
    pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, bumpedIndex]

theorem child_fields (c : List Bool)
    (hg : FixedWidthPolynomial.count (S.arity c) (S.sourceWidth c) ≤
      IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c))
    (hr : S.rank c ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c)) :
    let w := IntegralCriticalFlatDerivativeQuery.writer P (IntegralDerivativeBits.flatQuery S (input P S c))
    IntegralCriticalHistoryTask.get P .sourceIndex w = bumpedIndex P S c ∧
      IntegralCriticalHistoryTask.get P .row w = (IntegralCriticalFlatOriginalCoefficientBits.index P S.toSource .row c).val ∧
      IntegralCriticalHistoryTask.get P .col w = (IntegralCriticalFlatOriginalCoefficientBits.index P S.toSource .col c).val := by
  dsimp only
  rw [query_packet]
  exact IntegralCriticalFlatDerivativeQuery.writer_packet_fields P c _ _ _
    ((bumpedIndex_lt P S c).le.trans hg)
    ((IntegralCriticalFlatOriginalCoefficientBits.index P S.toSource .row c).isLt.le.trans hr)
    ((IntegralCriticalFlatOriginalCoefficientBits.index P S.toSource .col c).isLt.le.trans hr)

theorem coefficient_reply (c : List Bool) :
    letI := S.ring c
    b.coefficient (IntegralDerivativeBits.flatQuery S (input P S c)) = residueBits
      ((Algebra.leftMulMatrix (S.basis c) ((S.polynomial c).coeff
        (RationalSubstitution.Indexed.exponentVector (S.arity c)
          (FixedWidthPolynomial.entry (S.sourceWidth c) (bumpedIndex P S c))))
        (IntegralCriticalFlatOriginalCoefficientBits.index P S.toSource .row c)
        (IntegralCriticalFlatOriginalCoefficientBits.index P S.toSource .col c) : ℤ) : ZMod (S.modulus c)) := by
  rw [query_packet]
  exact b.coefficient_eq c _ _ _

noncomputable def stateBound (c : List Bool) : ℕ :=
  2 * (input P S c).length + 4 + (S.modulus c).size

include a b in
theorem stateBound_unary : UnaryFn (stateBound P S) := by
  have HM : UnaryFn (fun c => (S.modulus c).size) :=
    (UnaryFn.length b.modulus.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 2).mul (UnaryFn.length (input_FP P a S b))).add (UnaryFn.const 4)).add HM

theorem state_length (answer : List Bool → List Bool) (he : Replies P S b answer) (c : List Bool) (t : ℕ) :
    (SingleCall.encState (((controller P S).reference answer)^[t] ((controller P S).initial c))).length ≤
      stateBound P S c := by
  classical
  simp only [controller, RecursiveController.Controller.prepare_orbit, SingleCall.Program.controller]
  apply (program P S).state_length_of_bound answer (input P S c) t (S.modulus c).size
  intro hr
  have hrq : IntegralDerivativeBits.flatRequest S (input P S c) := by
    change decide (IntegralDerivativeBits.flatRequest S (input P S c)) = true at hr
    exact of_decide_eq_true hr
  change (answer (IntegralCriticalFlatDerivativeQuery.writer P
    (IntegralDerivativeBits.flatQuery S (input P S c)))).length ≤ _
  rw [he c hrq]
  let := S.ring c
  rw [coefficient_reply]
  have : NeZero (S.modulus c) := ⟨S.modulus_ne_zero c⟩
  rw [← BinaryNatCode.length_encode]
  apply ModularFold.bits_length_le (fun c => BinaryNatCode.encode (S.modulus c)) c
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using ZMod.val_lt _

theorem requests_iff (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool) :
    (controller P S).Requests answer budget c child ↔
      IntegralDerivativeBits.flatRequest S (input P S c) ∧
      child = IntegralCriticalFlatDerivativeQuery.writer P (IntegralDerivativeBits.flatQuery S (input P S c)) := by
  rw [controller, RecursiveController.Controller.prepare_requests_iff]
  simpa only [program, IntegralDerivativeBits.program, IntegralDerivativeBits.flatRequest,
    IntegralDerivativeBits.flatQuery, Function.comp_apply] using
    FixedWidthDerivativeBits.program_requests_iff (IntegralDerivativeBits.arity S) (IntegralDerivativeBits.width S)
      (IntegralDerivativeBits.width S) (IntegralDerivativeBits.degree S) (IntegralDerivativeBits.selected S)
      pairSnd (IntegralDerivativeBits.modulus S)
      (IntegralCriticalFlatDerivativeQuery.writer P ∘ IntegralDerivativeBits.coefficientQuery)
      answer (fun _ => budget c) (input P S c) child

theorem requests_rank (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .derivativeCoefficient c)
    (hc : (controller P S).Requests answer budget c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨_, rfl⟩ := (requests_iff P S answer budget c child).mp hc
  have H := IntegralCriticalFlatDerivativeQuery.writer_lower_rank P (IntegralDerivativeBits.flatQuery S (input P S c))
  rw [IntegralDerivativeBits.flatQuery_original, input_original] at H
  exact H hp

theorem requests_tasks (answer : List Bool → List Bool) (budget : List Bool → ℕ) (root c child : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P root c)
    (hc : (controller P S).Requests answer budget c child) : IntegralCriticalHistoryTask.Tasks P root child := by
  obtain ⟨_, rfl⟩ := (requests_iff P S answer budget c child).mp hc
  apply IntegralCriticalFlatDerivativeQuery.writer_tasks
  rw [IntegralDerivativeBits.flatQuery_original, input_original]
  exact ht

noncomputable def eulerSource (E : IntegralEulerBits.Source) := IntegralCriticalFlatGridSourceBits.derivativeInput P E
noncomputable def eulerAccess (E : IntegralEulerBits.Source) (hb : IntegralEulerBits.Access E) :
    IntegralDerivativeBits.Access (eulerSource P E) := IntegralCriticalFlatGridSourceBits.derivativeInputAccess P a E hb

end LeanCanny.Algebra.IntegralCriticalFlatDerivativeBits

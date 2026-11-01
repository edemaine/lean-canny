/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatMonomial
public import LeanCanny.Algebra.IntegralCriticalFlatGenericGrid
/-! # Native flat factors for arbitrary actual monomial sources -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatGenericMonomialBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks

def coefficientTask (P : IntegralCriticalHistoryTask.Parameters) (p : List Bool) : List Bool :=
  if IntegralCriticalHistoryTask.get P .expression (pairFst p) = 1 then
    IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient p
  else IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient p

theorem coefficientTask_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P) :
    coefficientTask P ∈ FP := by
  have HE : BinaryFn (fun p => IntegralCriticalHistoryTask.get P .expression (pairFst p)) :=
    (IntegralCriticalHistoryTask.get_binary P a .expression).comp pairFst_mem_FP
  exact (HE.eq (BinaryFn.const 1)).ite_mem_FP
    (IntegralCriticalFlatMatrixQuery.writer_FP P a .derivativeCoefficient)
    (IntegralCriticalFlatMatrixQuery.writer_FP P a .originalCoefficient)

variable (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralMonomialTermBits.Source) (h : IntegralMonomialTermBits.Access F) (n : h.denominator ∈ FP)

noncomputable def index (f : IntegralCriticalHistoryTask.Field) (c : List Bool) :
    Fin (F.rank c) :=
  ⟨IntegralCriticalHistoryTask.get P f c % F.rank c,
    Nat.mod_lt _ (Nat.zero_le _ |>.trans_lt (F.row c).isLt)⟩

noncomputable def input (c : List Bool) : List Bool :=
  IntegralMonomialTermBits.packet c (IntegralCriticalHistoryTask.get P .slot8 c)
    (index P F .row c).val (index P F .col c).val

include a h in
theorem input_FP : input P F ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair (IntegralCriticalHistoryTask.get_binary P a .slot8).bits_mem_FP
    (mem_FP_pair ((IntegralCriticalHistoryTask.get_binary P a .row).mod
      h.rank).bits_mem_FP
      ((IntegralCriticalHistoryTask.get_binary P a .col).mod
        h.rank).bits_mem_FP))

theorem input_parent (c : List Bool) : pairFst (input P F c) = c := by
  unfold input IntegralMonomialTermBits.packet
  exact pairFst_pair _ _

noncomputable def program :=
  IntegralMonomialTermBits.EntryStage.program F
    h (coefficientTask P)
    (IntegralCriticalFlatFactorQuery.writer P .clearedHeight)

noncomputable def controller := (program P F h).controller.prepare (input P F)

include a n in
theorem controls : (program P F h).Controls :=
  IntegralMonomialTermBits.EntryStage.controls F
    h
    (n) _ _
    (coefficientTask_FP P a) (IntegralCriticalFlatFactorQuery.writer_FP P a .clearedHeight)

include a n in
theorem certificates : (controller P F h).Certificates (encQ := encBits) (encS := SingleCall.encState) :=
  (program P F h).controller.prepare_certificates _ ((program P F h).certificates (controls P a F h n))
    (input_FP P a F h)

abbrev CoefficientReplies (answer : List Bool → List Bool) : Prop :=
  ∀ c, IntegralMonomialTermBits.position (input P F c) = 0 →
    answer (coefficientTask P (IntegralMonomialTermBits.coefficientQuery (input P F c))) =
      h.coefficient
        (IntegralMonomialTermBits.coefficientQuery (input P F c))
abbrev HeightReplies (answer : List Bool → List Bool) : Prop :=
  ∀ c, IntegralMonomialTermBits.EntryStage.request F
      (input P F c) →
    IntegralMonomialTermBits.position (input P F c) ≠ 0 →
    answer (IntegralCriticalFlatFactorQuery.writer P .clearedHeight
      (IntegralMonomialTermBits.heightQuery (input P F c))) =
      h.height
        (IntegralMonomialTermBits.heightQuery (input P F c))

theorem value (answer : List Bool → List Bool) (hc : CoefficientReplies P F h answer)
    (hh : HeightReplies P F h answer) (c : List Bool) :
    (program P F h).value answer (input P F c) =
      IntegralMonomialTermBits.entryProgram _ h
        (input P F c) :=
  IntegralMonomialTermBits.EntryStage.value_eq_at F
    h (coefficientTask P)
    (IntegralCriticalFlatFactorQuery.writer P .clearedHeight) answer (input P F c) (hc c) (hh c)

theorem halted_after (answer : List Bool → List Bool) (c : List Bool) :
    (controller P F h).halted (((controller P F h).reference answer)^[1]
      ((controller P F h).initial c)) = true := by
  simpa only [controller, RecursiveController.Controller.prepare_halted_iterate, SingleCall.Program.controller] using
    (program P F h).halted_after answer (input P F c)

theorem output_when_halted (answer : List Bool → List Bool) (hc : CoefficientReplies P F h answer)
    (hh : HeightReplies P F h answer) (c : List Bool) (t : ℕ)
    (hs : (controller P F h).halted (((controller P F h).reference answer)^[t]
      ((controller P F h).initial c)) = true) :
    (controller P F h).output (((controller P F h).reference answer)^[t]
      ((controller P F h).initial c)) =
      IntegralMonomialTermBits.entryProgram _ h
        (input P F c) :=
  by
    simp only [controller, RecursiveController.Controller.prepare_halted_iterate, SingleCall.Program.controller] at hs
    simpa only [controller, RecursiveController.Controller.prepare_output_iterate, SingleCall.Program.controller] using
      ((program P F h).output_when_halted answer (input P F c) t hs).trans
        (value P F h answer hc hh c)

theorem actual_value (answer : List Bool → List Bool) (hc : CoefficientReplies P F h answer)
    (hh : HeightReplies P F h answer) (c : List Bool) :
    let := F.ring c
    (program P F h).value answer (input P F c) = residueBits
      ((Algebra.leftMulMatrix (F.basis c)
        (IntegralMonomialTermBits.factor F c
          (IntegralCriticalHistoryTask.get P .slot8 c)) (index P F .row c) (index P F .col c) : ℤ) :
        ZMod (F.modulus c)) := by
  exact (value P F h answer hc hh c).trans
    (IntegralMonomialTermBits.entry_correct F
      h c _ (index P F .row c) (index P F .col c))

noncomputable def stateBound (c : List Bool) : ℕ :=
  2 * (input P F c).length + 4 + (F.modulus c).size

include a h in
theorem stateBound_unary : UnaryFn (stateBound P F) := by
  have HM : UnaryFn (fun c => (F.modulus c).size) :=
    (UnaryFn.length h.modulus.bits_mem_FP).of_eq
      (fun _ => BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 2).mul (UnaryFn.length (input_FP P a F h))).add (UnaryFn.const 4)).add HM

theorem state_length (answer : List Bool → List Bool) (hc : CoefficientReplies P F h answer)
    (hh : HeightReplies P F h answer) (c : List Bool) (t : ℕ) :
    (SingleCall.encState (((controller P F h).reference answer)^[t]
      ((controller P F h).initial c))).length ≤ stateBound P F c := by
  simp only [controller, RecursiveController.Controller.prepare_orbit, SingleCall.Program.controller]
  apply (program P F h).state_length_of_bound answer (input P F c) t
    (F.modulus c).size
  intro hr
  let := F.ring c
  have HV := actual_value P F h answer hc hh c
  rw [SingleCall.Program.value, hr, ite_eq_left rfl] at HV
  have HQ : (program P F h).finish = pairSnd := rfl
  rw [HQ, pairSnd_pair] at HV
  rw [HV]
  have : NeZero (F.modulus c) :=
    ⟨F.modulus_ne_zero c⟩
  rw [← BinaryNatCode.length_encode]
  apply ModularFold.bits_length_le
    (fun c => BinaryNatCode.encode (F.modulus c)) c
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using ZMod.val_lt _

theorem requests_iff (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool) :
    (controller P F h).Requests answer budget c child ↔
      IntegralMonomialTermBits.EntryStage.request F
        (input P F c) ∧
      child = if IntegralMonomialTermBits.position (input P F c) = 0 then
        coefficientTask P (IntegralMonomialTermBits.coefficientQuery (input P F c))
      else IntegralCriticalFlatFactorQuery.writer P .clearedHeight
        (IntegralMonomialTermBits.heightQuery (input P F c)) := by
  rw [controller, RecursiveController.Controller.prepare_requests_iff]
  exact IntegralMonomialTermBits.EntryStage.requests_iff F
    h (coefficientTask P)
    (IntegralCriticalFlatFactorQuery.writer P .clearedHeight) answer _ _ _

theorem coefficientQuery_parent (c : List Bool) :
    pairFst (IntegralMonomialTermBits.coefficientQuery (input P F c)) = c := by
  simp only [IntegralMonomialTermBits.coefficientQuery, pairFst_pair, input_parent]

theorem heightQuery_parent (c : List Bool) :
    pairFst (IntegralMonomialTermBits.heightQuery (input P F c)) = c := by
  simp only [IntegralMonomialTermBits.heightQuery, pairFst_pair, input_parent]

theorem height_coordinate (c : List Bool) :
    IntegralCriticalHistoryTask.get P .slot8 (IntegralCriticalFlatFactorQuery.writer P .clearedHeight
      (IntegralMonomialTermBits.heightQuery (input P F c))) =
      IntegralCriticalHistoryTask.get P .slot8 c - 2 := by
  rw [IntegralCriticalFlatFactorQuery.writer_get]
  simp only [reduceCtorEq, ite_false, ite_true, IntegralMonomialTermBits.heightQuery,
    IntegralMonomialTermBits.index, IntegralMonomialTermBits.position, IntegralPowerProductBits.factorWord,
    input, IntegralMonomialTermBits.packet, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact min_eq_left ((Nat.sub_le _ _).trans (IntegralCriticalHistoryTask.get_le P .slot8 c))

theorem requests_rank (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .monomialFactor c)
    (hc : (controller P F h).Requests answer budget c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨_, rfl⟩ := (requests_iff P F h answer budget c child).mp hc
  change IntegralCriticalHistoryTask.phase c = 3 at hp
  split_ifs with hz
  · unfold coefficientTask
    split_ifs
    · have HL := IntegralCriticalFlatMatrixQuery.writer_lower_rank P .derivativeCoefficient
        (IntegralMonomialTermBits.coefficientQuery (input P F c))
      rw [coefficientQuery_parent] at HL
      exact HL (by change 1 < IntegralCriticalHistoryTask.phase c; omega)
    · have HL := IntegralCriticalFlatMatrixQuery.writer_lower_rank P .originalCoefficient
        (IntegralMonomialTermBits.coefficientQuery (input P F c))
      rw [coefficientQuery_parent] at HL
      exact HL (by change 0 < IntegralCriticalHistoryTask.phase c; omega)
  · have HL := IntegralCriticalFlatFactorQuery.writer_lower_rank P .clearedHeight
      (IntegralMonomialTermBits.heightQuery (input P F c))
    rw [heightQuery_parent] at HL
    exact HL (by change 2 < IntegralCriticalHistoryTask.phase c; omega)

theorem requests_tasks (answer : List Bool → List Bool) (budget : List Bool → ℕ) (root c child : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P root c)
    (hc : (controller P F h).Requests answer budget c child) :
    IntegralCriticalHistoryTask.Tasks P root child := by
  obtain ⟨_, rfl⟩ := (requests_iff P F h answer budget c child).mp hc
  split_ifs
  · unfold coefficientTask
    split_ifs <;> apply IntegralCriticalFlatMatrixQuery.writer_tasks <;>
      simpa only [coefficientQuery_parent] using ht
  · apply IntegralCriticalFlatFactorQuery.writer_tasks
    simpa only [heightQuery_parent] using ht

abbrev CoefficientRepliesAt (answer : List Bool → List Bool) (c : List Bool) : Prop :=
   IntegralMonomialTermBits.position (input P F c) = 0 →
    answer (coefficientTask P (IntegralMonomialTermBits.coefficientQuery (input P F c))) =
      h.coefficient
        (IntegralMonomialTermBits.coefficientQuery (input P F c))
abbrev HeightRepliesAt (answer : List Bool → List Bool) (c : List Bool) : Prop :=
   IntegralMonomialTermBits.EntryStage.request F
      (input P F c) →
    IntegralMonomialTermBits.position (input P F c) ≠ 0 →
    answer (IntegralCriticalFlatFactorQuery.writer P .clearedHeight
      (IntegralMonomialTermBits.heightQuery (input P F c))) =
      h.height
        (IntegralMonomialTermBits.heightQuery (input P F c))


theorem value_at (answer : List Bool → List Bool) (c : List Bool) (hc : CoefficientRepliesAt P F h answer c)
    (hh : HeightRepliesAt P F h answer c) :
    (program P F h).value answer (input P F c) =
      IntegralMonomialTermBits.entryProgram _ h
        (input P F c) :=
  IntegralMonomialTermBits.EntryStage.value_eq_at F
    h (coefficientTask P)
    (IntegralCriticalFlatFactorQuery.writer P .clearedHeight) answer (input P F c) hc hh

theorem actual_value_at (answer : List Bool → List Bool) (c : List Bool) (hc : CoefficientRepliesAt P F h answer c)
    (hh : HeightRepliesAt P F h answer c) :
    let := F.ring c
    (program P F h).value answer (input P F c) = residueBits
      ((Algebra.leftMulMatrix (F.basis c)
        (IntegralMonomialTermBits.factor F c
          (IntegralCriticalHistoryTask.get P .slot8 c)) (index P F .row c) (index P F .col c) : ℤ) :
        ZMod (F.modulus c)) := by
  exact (value_at P F h answer c hc hh).trans
    (IntegralMonomialTermBits.entry_correct F
      h c _ (index P F .row c) (index P F .col c))

theorem state_length_at (answer : List Bool → List Bool) (c : List Bool) (hc : CoefficientRepliesAt P F h answer c)
    (hh : HeightRepliesAt P F h answer c) (t : ℕ) :
    (SingleCall.encState (((controller P F h).reference answer)^[t]
      ((controller P F h).initial c))).length ≤ stateBound P F c := by
  simp only [controller, RecursiveController.Controller.prepare_orbit, SingleCall.Program.controller]
  apply (program P F h).state_length_of_bound answer (input P F c) t
    (F.modulus c).size
  intro hr
  let := F.ring c
  have HV := actual_value_at P F h answer c hc hh
  rw [SingleCall.Program.value, hr, ite_eq_left rfl] at HV
  have HQ : (program P F h).finish = pairSnd := rfl
  rw [HQ, pairSnd_pair] at HV
  rw [HV]
  have : NeZero (F.modulus c) :=
    ⟨F.modulus_ne_zero c⟩
  rw [← BinaryNatCode.length_encode]
  apply ModularFold.bits_length_le
    (fun c => BinaryNatCode.encode (F.modulus c)) c
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using ZMod.val_lt _

theorem output_when_halted_at (answer : List Bool → List Bool) (c : List Bool) (hc : CoefficientRepliesAt P F h answer c)
    (hh : HeightRepliesAt P F h answer c) (t : ℕ)
    (hs : (controller P F h).halted (((controller P F h).reference answer)^[t]
      ((controller P F h).initial c)) = true) :
    (controller P F h).output (((controller P F h).reference answer)^[t]
      ((controller P F h).initial c)) =
      IntegralMonomialTermBits.entryProgram _ h
        (input P F c) :=
  by
    simp only [controller, RecursiveController.Controller.prepare_halted_iterate, SingleCall.Program.controller] at hs
    simpa only [controller, RecursiveController.Controller.prepare_output_iterate, SingleCall.Program.controller] using
      ((program P F h).output_when_halted answer (input P F c) t hs).trans
        (value_at P F h answer c hc hh)

end LeanCanny.Algebra.IntegralCriticalFlatGenericMonomialBits

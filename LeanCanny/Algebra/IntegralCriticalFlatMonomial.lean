/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatProductEntry

/-! # Actual flat coefficient, scalar and retained-height factors

Coefficient factors select phase 0 or 1 according to the source expression.
Retained-height factors use phase 2 with slot 8 replaced by the original
coordinate. Scalar factors use the native original common denominator.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMonomialTermBits.EntryStage
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical

theorem value_eq_at (S : Source) (a : Access S) (coefficientTask heightTask answer : List Bool → List Bool)
    (p : List Bool)
    (hc : position p = 0 → answer (coefficientTask (coefficientQuery p)) = a.coefficient (coefficientQuery p))
    (hh : request S p → position p ≠ 0 → answer (heightTask (heightQuery p)) = a.height (heightQuery p)) :
    (program S a coefficientTask heightTask).value answer p = entryProgram S a p := by
  by_cases h0 : position p = 0 <;> by_cases h1 : position p = 1 <;>
    by_cases hv : valid S p <;> by_cases hf : freeIndex S p <;>
    simp_all [SingleCall.Program.value, program, request, entryProgram]

end LeanCanny.Algebra.IntegralMonomialTermBits.EntryStage

namespace LeanCanny.Algebra.IntegralCriticalFlatMonomialBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks
attribute [local irreducible] IntegralCriticalFlatMonomialSourceBits.source IntegralCriticalFlatMonomialSourceBits.access
abbrev Queries := IntegralCriticalScriptGeneratorBits.Queries

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
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatCompanionBits.metadata F))

noncomputable def index (f : IntegralCriticalHistoryTask.Field) (c : List Bool) :
    Fin ((IntegralCriticalFlatMonomialSourceBits.source P F q).rank c) :=
  ⟨IntegralCriticalHistoryTask.get P f c % (IntegralCriticalFlatMonomialSourceBits.source P F q).rank c,
    Nat.mod_lt _ (Nat.zero_le _ |>.trans_lt ((IntegralCriticalFlatMonomialSourceBits.source P F q).row c).isLt)⟩

noncomputable def input (c : List Bool) : List Bool :=
  IntegralMonomialTermBits.packet c (IntegralCriticalHistoryTask.get P .slot8 c)
    (index P F q .row c).val (index P F q .col c).val

include a h in
theorem input_FP : input P F q ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair (IntegralCriticalHistoryTask.get_binary P a .slot8).bits_mem_FP
    (mem_FP_pair ((IntegralCriticalHistoryTask.get_binary P a .row).mod
      (IntegralCriticalFlatMonomialSourceBits.access P a F q h).rank).bits_mem_FP
      ((IntegralCriticalHistoryTask.get_binary P a .col).mod
        (IntegralCriticalFlatMonomialSourceBits.access P a F q h).rank).bits_mem_FP))

theorem input_parent (c : List Bool) : pairFst (input P F q c) = c := by
  unfold input IntegralMonomialTermBits.packet
  exact pairFst_pair _ _

noncomputable def program :=
  IntegralMonomialTermBits.EntryStage.program (IntegralCriticalFlatMonomialSourceBits.source P F q)
    (IntegralCriticalFlatMonomialSourceBits.access P a F q h) (coefficientTask P)
    (IntegralCriticalFlatFactorQuery.writer P .clearedHeight)

noncomputable def controller := (program P a F q h).controller.prepare (input P F q)

include n in
theorem controls : (program P a F q h).Controls :=
  IntegralMonomialTermBits.EntryStage.controls (IntegralCriticalFlatMonomialSourceBits.source P F q)
    (IntegralCriticalFlatMonomialSourceBits.access P a F q h)
    (IntegralCriticalFlatMonomialSourceBits.denominator_FP P a F q h n) _ _
    (coefficientTask_FP P a) (IntegralCriticalFlatFactorQuery.writer_FP P a .clearedHeight)

include n in
theorem certificates : (controller P a F q h).Certificates (encQ := encBits) (encS := SingleCall.encState) :=
  (program P a F q h).controller.prepare_certificates _ ((program P a F q h).certificates (controls P a F q h n))
    (input_FP P a F q h)

abbrev CoefficientReplies (answer : List Bool → List Bool) : Prop :=
  ∀ c, IntegralMonomialTermBits.position (input P F q c) = 0 →
    answer (coefficientTask P (IntegralMonomialTermBits.coefficientQuery (input P F q c))) =
      (IntegralCriticalFlatMonomialSourceBits.access P a F q h).coefficient
        (IntegralMonomialTermBits.coefficientQuery (input P F q c))
abbrev HeightReplies (answer : List Bool → List Bool) : Prop :=
  ∀ c, IntegralMonomialTermBits.EntryStage.request (IntegralCriticalFlatMonomialSourceBits.source P F q)
      (input P F q c) →
    IntegralMonomialTermBits.position (input P F q c) ≠ 0 →
    answer (IntegralCriticalFlatFactorQuery.writer P .clearedHeight
      (IntegralMonomialTermBits.heightQuery (input P F q c))) =
      (IntegralCriticalFlatMonomialSourceBits.access P a F q h).height
        (IntegralMonomialTermBits.heightQuery (input P F q c))

theorem value (answer : List Bool → List Bool) (hc : CoefficientReplies P a F q h answer)
    (hh : HeightReplies P a F q h answer) (c : List Bool) :
    (program P a F q h).value answer (input P F q c) =
      IntegralMonomialTermBits.entryProgram _ (IntegralCriticalFlatMonomialSourceBits.access P a F q h)
        (input P F q c) :=
  IntegralMonomialTermBits.EntryStage.value_eq_at (IntegralCriticalFlatMonomialSourceBits.source P F q)
    (IntegralCriticalFlatMonomialSourceBits.access P a F q h) (coefficientTask P)
    (IntegralCriticalFlatFactorQuery.writer P .clearedHeight) answer (input P F q c) (hc c) (hh c)

theorem halted_after (answer : List Bool → List Bool) (c : List Bool) :
    (controller P a F q h).halted (((controller P a F q h).reference answer)^[1]
      ((controller P a F q h).initial c)) = true := by
  simpa only [controller, RecursiveController.Controller.prepare_halted_iterate, SingleCall.Program.controller] using
    (program P a F q h).halted_after answer (input P F q c)

theorem output_when_halted (answer : List Bool → List Bool) (hc : CoefficientReplies P a F q h answer)
    (hh : HeightReplies P a F q h answer) (c : List Bool) (t : ℕ)
    (hs : (controller P a F q h).halted (((controller P a F q h).reference answer)^[t]
      ((controller P a F q h).initial c)) = true) :
    (controller P a F q h).output (((controller P a F q h).reference answer)^[t]
      ((controller P a F q h).initial c)) =
      IntegralMonomialTermBits.entryProgram _ (IntegralCriticalFlatMonomialSourceBits.access P a F q h)
        (input P F q c) :=
  by
    simp only [controller, RecursiveController.Controller.prepare_halted_iterate, SingleCall.Program.controller] at hs
    simpa only [controller, RecursiveController.Controller.prepare_output_iterate, SingleCall.Program.controller] using
      ((program P a F q h).output_when_halted answer (input P F q c) t hs).trans
        (value P a F q h answer hc hh c)

theorem actual_value (answer : List Bool → List Bool) (hc : CoefficientReplies P a F q h answer)
    (hh : HeightReplies P a F q h answer) (c : List Bool) :
    let := (IntegralCriticalFlatMonomialSourceBits.source P F q).ring c
    (program P a F q h).value answer (input P F q c) = residueBits
      ((Algebra.leftMulMatrix ((IntegralCriticalFlatMonomialSourceBits.source P F q).basis c)
        (IntegralMonomialTermBits.factor (IntegralCriticalFlatMonomialSourceBits.source P F q) c
          (IntegralCriticalHistoryTask.get P .slot8 c)) (index P F q .row c) (index P F q .col c) : ℤ) :
        ZMod ((IntegralCriticalFlatMonomialSourceBits.source P F q).modulus c)) := by
  exact (value P a F q h answer hc hh c).trans
    (IntegralMonomialTermBits.entry_correct (IntegralCriticalFlatMonomialSourceBits.source P F q)
      (IntegralCriticalFlatMonomialSourceBits.access P a F q h) c _ (index P F q .row c) (index P F q .col c))

noncomputable def stateBound (c : List Bool) : ℕ :=
  2 * (input P F q c).length + 4 + ((IntegralCriticalFlatMonomialSourceBits.source P F q).modulus c).size

include a h in
theorem stateBound_unary : UnaryFn (stateBound P F q) := by
  have HM : UnaryFn (fun c => ((IntegralCriticalFlatMonomialSourceBits.source P F q).modulus c).size) :=
    (UnaryFn.length (IntegralCriticalFlatMonomialSourceBits.access P a F q h).modulus.bits_mem_FP).of_eq
      (fun _ => BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 2).mul (UnaryFn.length (input_FP P a F q h))).add (UnaryFn.const 4)).add HM

theorem state_length (answer : List Bool → List Bool) (hc : CoefficientReplies P a F q h answer)
    (hh : HeightReplies P a F q h answer) (c : List Bool) (t : ℕ) :
    (SingleCall.encState (((controller P a F q h).reference answer)^[t]
      ((controller P a F q h).initial c))).length ≤ stateBound P F q c := by
  simp only [controller, RecursiveController.Controller.prepare_orbit, SingleCall.Program.controller]
  apply (program P a F q h).state_length_of_bound answer (input P F q c) t
    ((IntegralCriticalFlatMonomialSourceBits.source P F q).modulus c).size
  intro hr
  let := (IntegralCriticalFlatMonomialSourceBits.source P F q).ring c
  have HV := actual_value P a F q h answer hc hh c
  rw [SingleCall.Program.value, hr, ite_eq_left rfl] at HV
  have HQ : (program P a F q h).finish = pairSnd := rfl
  rw [HQ, pairSnd_pair] at HV
  rw [HV]
  have : NeZero ((IntegralCriticalFlatMonomialSourceBits.source P F q).modulus c) :=
    ⟨(IntegralCriticalFlatMonomialSourceBits.source P F q).modulus_ne_zero c⟩
  rw [← BinaryNatCode.length_encode]
  apply ModularFold.bits_length_le
    (fun c => BinaryNatCode.encode ((IntegralCriticalFlatMonomialSourceBits.source P F q).modulus c)) c
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using ZMod.val_lt _

theorem requests_iff (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool) :
    (controller P a F q h).Requests answer budget c child ↔
      IntegralMonomialTermBits.EntryStage.request (IntegralCriticalFlatMonomialSourceBits.source P F q)
        (input P F q c) ∧
      child = if IntegralMonomialTermBits.position (input P F q c) = 0 then
        coefficientTask P (IntegralMonomialTermBits.coefficientQuery (input P F q c))
      else IntegralCriticalFlatFactorQuery.writer P .clearedHeight
        (IntegralMonomialTermBits.heightQuery (input P F q c)) := by
  rw [controller, RecursiveController.Controller.prepare_requests_iff]
  exact IntegralMonomialTermBits.EntryStage.requests_iff (IntegralCriticalFlatMonomialSourceBits.source P F q)
    (IntegralCriticalFlatMonomialSourceBits.access P a F q h) (coefficientTask P)
    (IntegralCriticalFlatFactorQuery.writer P .clearedHeight) answer _ _ _

theorem coefficientQuery_parent (c : List Bool) :
    pairFst (IntegralMonomialTermBits.coefficientQuery (input P F q c)) = c := by
  simp only [IntegralMonomialTermBits.coefficientQuery, pairFst_pair, input_parent]

theorem heightQuery_parent (c : List Bool) :
    pairFst (IntegralMonomialTermBits.heightQuery (input P F q c)) = c := by
  simp only [IntegralMonomialTermBits.heightQuery, pairFst_pair, input_parent]

theorem height_coordinate (c : List Bool) :
    IntegralCriticalHistoryTask.get P .slot8 (IntegralCriticalFlatFactorQuery.writer P .clearedHeight
      (IntegralMonomialTermBits.heightQuery (input P F q c))) =
      IntegralCriticalHistoryTask.get P .slot8 c - 2 := by
  rw [IntegralCriticalFlatFactorQuery.writer_get]
  simp only [reduceCtorEq, ite_false, ite_true, IntegralMonomialTermBits.heightQuery,
    IntegralMonomialTermBits.index, IntegralMonomialTermBits.position, IntegralPowerProductBits.factorWord,
    input, IntegralMonomialTermBits.packet, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact min_eq_left ((Nat.sub_le _ _).trans (IntegralCriticalHistoryTask.get_le P .slot8 c))

theorem requests_rank (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .monomialFactor c)
    (hc : (controller P a F q h).Requests answer budget c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨_, rfl⟩ := (requests_iff P a F q h answer budget c child).mp hc
  change IntegralCriticalHistoryTask.phase c = 3 at hp
  split_ifs with hz
  · unfold coefficientTask
    split_ifs
    · have HL := IntegralCriticalFlatMatrixQuery.writer_lower_rank P .derivativeCoefficient
        (IntegralMonomialTermBits.coefficientQuery (input P F q c))
      rw [coefficientQuery_parent] at HL
      exact HL (by change 1 < IntegralCriticalHistoryTask.phase c; omega)
    · have HL := IntegralCriticalFlatMatrixQuery.writer_lower_rank P .originalCoefficient
        (IntegralMonomialTermBits.coefficientQuery (input P F q c))
      rw [coefficientQuery_parent] at HL
      exact HL (by change 0 < IntegralCriticalHistoryTask.phase c; omega)
  · have HL := IntegralCriticalFlatFactorQuery.writer_lower_rank P .clearedHeight
      (IntegralMonomialTermBits.heightQuery (input P F q c))
    rw [heightQuery_parent] at HL
    exact HL (by change 2 < IntegralCriticalHistoryTask.phase c; omega)

theorem requests_tasks (answer : List Bool → List Bool) (budget : List Bool → ℕ) (root c child : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P root c)
    (hc : (controller P a F q h).Requests answer budget c child) :
    IntegralCriticalHistoryTask.Tasks P root child := by
  obtain ⟨_, rfl⟩ := (requests_iff P a F q h answer budget c child).mp hc
  split_ifs
  · unfold coefficientTask
    split_ifs <;> apply IntegralCriticalFlatMatrixQuery.writer_tasks <;>
      simpa only [coefficientQuery_parent] using ht
  · apply IntegralCriticalFlatFactorQuery.writer_tasks
    simpa only [heightQuery_parent] using ht

end LeanCanny.Algebra.IntegralCriticalFlatMonomialBits

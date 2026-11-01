/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatProduct

/-! # Fresh factor-power children of actual layered product entries -/

@[expose] public section
namespace LeanCanny.Algebra.MatrixProductBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation

theorem entry_value_at (S : Family) (a : Access S) (task answer : List Bool → List Bool) (p : List Bool)
    (he : adjacent S p → answer (task (factorQuery S p)) = a.entry (factorQuery S p)) :
    (entryProgram S task).value answer p = powerEntry S a p := by
  simp only [SingleCall.Program.value, entryProgram, decide_eq_true_eq, pairSnd_pair]
  change (if adjacent S p then answer (task (factorQuery S p)) else []) =
    (if adjacent S p then a.entry (factorQuery S p) else [])
  by_cases hp : adjacent S p
  · simp only [ite_eq_left hp]
    exact he hp
  · simp only [ite_eq_right hp]

end LeanCanny.Algebra.MatrixProductBits.RecursiveStage

namespace LeanCanny.Algebra.IntegralCriticalFlatProductEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks
attribute [local irreducible] IntegralCriticalFlatProductBits.family IntegralCriticalFlatProductBits.access
abbrev Queries := IntegralCriticalScriptGeneratorBits.Queries
variable (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q)

noncomputable def dimension (c : List Bool) : ℕ :=
  ((IntegralCriticalFlatProductBits.family P F q).count c + 1) * (IntegralCriticalFlatProductBits.family P F q).rank c

theorem dimension_pos (c : List Bool) : 0 < dimension P F q c :=
  Nat.mul_pos (Nat.succ_pos _) (Nat.zero_le _ |>.trans_lt ((IntegralCriticalFlatProductBits.family P F q).row c).isLt)

noncomputable def index (f : IntegralCriticalHistoryTask.Field) (c : List Bool) : Fin (dimension P F q c) :=
  ⟨IntegralCriticalHistoryTask.get P f c % dimension P F q c, Nat.mod_lt _ (dimension_pos P F q c)⟩

noncomputable def input (c : List Bool) : List Bool :=
  pair c (pair (BinaryNatCode.encode (index P F q .row c).val) (BinaryNatCode.encode (index P F q .col c).val))

include a h in
theorem dimension_binary : BinaryFn (dimension P F q) :=
  ((IntegralCriticalFlatProductBits.access P a F q h).count.add (BinaryFn.const 1)).mul
    (IntegralCriticalFlatProductBits.access P a F q h).rank

include a h in
theorem input_FP : input P F q ∈ FP :=
  mem_FP_pair id_mem_FP
    (mem_FP_pair ((IntegralCriticalHistoryTask.get_binary P a .row).mod (dimension_binary P a F q h)).bits_mem_FP
      ((IntegralCriticalHistoryTask.get_binary P a .col).mod (dimension_binary P a F q h)).bits_mem_FP)

noncomputable def program :=
  IntegralPowerProductBits.ProductStage.entryProgram (IntegralCriticalFlatProductBits.family P F q)
    (IntegralCriticalFlatFactorQuery.writer P .factorPower)

noncomputable def controller := (program P F q).controller.prepare (input P F q)

include a h in
theorem controls : (program P F q).Controls :=
  IntegralPowerProductBits.ProductStage.entry_controls _ (IntegralCriticalFlatProductBits.access P a F q h) _
    (IntegralCriticalFlatFactorQuery.writer_FP P a .factorPower)

include a h in
theorem certificates : (controller P F q).Certificates (encQ := encBits) (encS := SingleCall.encState) :=
  (program P F q).controller.prepare_certificates _ ((program P F q).certificates (controls P a F q h))
    (input_FP P a F q h)

abbrev Replies (answer : List Bool → List Bool) : Prop :=
  ∀ c, MatrixProductBits.RecursiveStage.adjacent
      (IntegralPowerProductBits.productFamily (IntegralCriticalFlatProductBits.family P F q)) (input P F q c) →
    answer (IntegralCriticalFlatFactorQuery.writer P .factorPower
      (MatrixProductBits.factorQuery (IntegralPowerProductBits.productFamily (IntegralCriticalFlatProductBits.family P F q))
        (input P F q c))) =
      (IntegralPowerProductBits.powerFamily (IntegralCriticalFlatProductBits.family P F q)).value
        (MatrixProductBits.factorQuery (IntegralPowerProductBits.productFamily (IntegralCriticalFlatProductBits.family P F q))
          (input P F q c))

include a h in
theorem value (answer : List Bool → List Bool) (he : Replies P F q answer) (c : List Bool) :
    (program P F q).value answer (input P F q c) =
      residueBits ((IntegralPowerProductBits.productFamily (IntegralCriticalFlatProductBits.family P F q)).power.matrix c
        (index P F q .row c) (index P F q .col c)) := by
  exact (MatrixProductBits.RecursiveStage.entry_value_at
    (IntegralPowerProductBits.productFamily (IntegralCriticalFlatProductBits.family P F q))
    (IntegralPowerProductBits.productAccess (IntegralCriticalFlatProductBits.family P F q)
      (IntegralCriticalFlatProductBits.access P a F q h))
    (IntegralCriticalFlatFactorQuery.writer P .factorPower) answer (input P F q c) (he c)).trans
    (MatrixProductBits.powerEntry_packet
      (IntegralPowerProductBits.productFamily (IntegralCriticalFlatProductBits.family P F q))
      (IntegralPowerProductBits.productAccess (IntegralCriticalFlatProductBits.family P F q)
        (IntegralCriticalFlatProductBits.access P a F q h)) c (index P F q .row c) (index P F q .col c))

theorem halted_after (answer : List Bool → List Bool) (c : List Bool) :
    (controller P F q).halted (((controller P F q).reference answer)^[1]
      ((controller P F q).initial c)) = true := by
  simpa only [controller, RecursiveController.Controller.prepare_halted_iterate, SingleCall.Program.controller] using
    (program P F q).halted_after answer (input P F q c)

include a h in
theorem output_when_halted (answer : List Bool → List Bool) (he : Replies P F q answer)
    (c : List Bool) (t : ℕ)
    (hh : (controller P F q).halted (((controller P F q).reference answer)^[t]
      ((controller P F q).initial c)) = true) :
    (controller P F q).output (((controller P F q).reference answer)^[t]
      ((controller P F q).initial c)) =
      residueBits ((IntegralPowerProductBits.productFamily (IntegralCriticalFlatProductBits.family P F q)).power.matrix c
        (index P F q .row c) (index P F q .col c)) := by
  simp only [controller, RecursiveController.Controller.prepare_halted_iterate, SingleCall.Program.controller] at hh
  simpa only [controller, RecursiveController.Controller.prepare_output_iterate, SingleCall.Program.controller] using
    ((program P F q).output_when_halted answer (input P F q c) t hh).trans (value P a F q h answer he c)

noncomputable def stateBound (c : List Bool) : ℕ :=
  2 * (input P F q c).length + 4 + ((IntegralCriticalFlatProductBits.family P F q).modulus c).size

theorem matrix_modulus (c : List Bool) :
    (IntegralPowerProductBits.productFamily (IntegralCriticalFlatProductBits.family P F q)).power.modulus c =
      (IntegralCriticalFlatProductBits.family P F q).modulus c := rfl

include a h in
theorem stateBound_unary : UnaryFn (stateBound P F q) := by
  have HM : UnaryFn (fun c => ((IntegralCriticalFlatProductBits.family P F q).modulus c).size) :=
    (UnaryFn.length (IntegralCriticalFlatProductBits.access P a F q h).modulus.bits_mem_FP).of_eq
      (fun _ => BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 2).mul (UnaryFn.length (input_FP P a F q h))).add (UnaryFn.const 4)).add HM

include a h in
theorem state_length (answer : List Bool → List Bool) (he : Replies P F q answer) (c : List Bool) (t : ℕ) :
    (SingleCall.encState (((controller P F q).reference answer)^[t]
      ((controller P F q).initial c))).length ≤ stateBound P F q c := by
  simp only [controller, RecursiveController.Controller.prepare_orbit, SingleCall.Program.controller]
  apply (program P F q).state_length_of_bound answer (input P F q c) t
    ((IntegralCriticalFlatProductBits.family P F q).modulus c).size
  intro hr
  have HV := value P a F q h answer he c
  rw [SingleCall.Program.value, hr, ite_eq_left rfl] at HV
  have HQ : (program P F q).finish = pairSnd := rfl
  rw [HQ, pairSnd_pair] at HV
  rw [HV]
  have : NeZero ((IntegralPowerProductBits.productFamily (IntegralCriticalFlatProductBits.family P F q)).power.modulus c) :=
    ⟨(IntegralPowerProductBits.productFamily (IntegralCriticalFlatProductBits.family P F q)).power.modulus_ne_zero c⟩
  rw [← BinaryNatCode.length_encode]
  apply ModularFold.bits_length_le
    (fun c => BinaryNatCode.encode ((IntegralCriticalFlatProductBits.family P F q).modulus c)) c
  have HLT := ZMod.val_lt ((IntegralPowerProductBits.productFamily (IntegralCriticalFlatProductBits.family P F q)).power.matrix c
    (index P F q .row c) (index P F q .col c))
  have HLT' := HLT.trans_eq (matrix_modulus P F q c)
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using HLT'

theorem requests_in_bounds (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool)
    (hc : (controller P F q).Requests answer budget c child) :
    ∃ s : Fin ((IntegralCriticalFlatProductBits.family P F q).count c),
    ∃ r t : Fin ((IntegralCriticalFlatProductBits.family P F q).rank c),
      child = IntegralCriticalFlatFactorQuery.writer P .factorPower (pair c
        (pair (BinaryNatCode.encode s.val) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) := by
  rw [controller, RecursiveController.Controller.prepare_requests_iff] at hc
  exact IntegralPowerProductBits.ProductStage.entry_requests_in_bounds (IntegralCriticalFlatProductBits.family P F q)
    (IntegralCriticalFlatFactorQuery.writer P .factorPower) answer _ c child
    (index P F q .row c) (index P F q .col c) hc

theorem requests_rank (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .productEntry c)
    (hc : (controller P F q).Requests answer budget c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨s, r, t, rfl⟩ := requests_in_bounds P F q answer budget c child hc
  have HL := IntegralCriticalFlatFactorQuery.writer_lower_rank P .factorPower
    (pair c (pair (BinaryNatCode.encode s.val) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))
  simp only [pairFst_pair] at HL
  apply HL
  change IntegralCriticalHistoryTask.phase c = 5 at hp
  change 4 < IntegralCriticalHistoryTask.phase c
  omega

theorem requests_tasks (answer : List Bool → List Bool) (budget : List Bool → ℕ) (root c child : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P root c)
    (hc : (controller P F q).Requests answer budget c child) :
    IntegralCriticalHistoryTask.Tasks P root child := by
  obtain ⟨s, r, t, rfl⟩ := requests_in_bounds P F q answer budget c child hc
  apply IntegralCriticalFlatFactorQuery.writer_tasks
  simpa only [pairFst_pair] using ht

end LeanCanny.Algebra.IntegralCriticalFlatProductEntryBits

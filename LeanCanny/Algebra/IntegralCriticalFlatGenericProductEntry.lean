/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatProductEntry
public import LeanCanny.Algebra.IntegralCriticalFlatGenericPower
/-! # Native layered product entries for arbitrary actual monomial sources -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatGenericProductEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks
variable (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralMonomialTermBits.Source) (h : IntegralMonomialTermBits.Access F)

noncomputable def dimension (c : List Bool) : ℕ :=
  ((IntegralMonomialTermBits.family F).count c + 1) * (IntegralMonomialTermBits.family F).rank c

theorem dimension_pos (c : List Bool) : 0 < dimension F c :=
  Nat.mul_pos (Nat.succ_pos _) (Nat.zero_le _ |>.trans_lt ((IntegralMonomialTermBits.family F).row c).isLt)

noncomputable def index (f : IntegralCriticalHistoryTask.Field) (c : List Bool) : Fin (dimension F c) :=
  ⟨IntegralCriticalHistoryTask.get P f c % dimension F c, Nat.mod_lt _ (dimension_pos F c)⟩

noncomputable def input (c : List Bool) : List Bool :=
  pair c (pair (BinaryNatCode.encode (index P F .row c).val) (BinaryNatCode.encode (index P F .col c).val))

include h in
theorem dimension_binary : BinaryFn (dimension F) :=
  ((IntegralMonomialTermBits.familyAccess F h).count.add (BinaryFn.const 1)).mul
    (IntegralMonomialTermBits.familyAccess F h).rank

include a h in
theorem input_FP : input P F ∈ FP :=
  mem_FP_pair id_mem_FP
    (mem_FP_pair ((IntegralCriticalHistoryTask.get_binary P a .row).mod (dimension_binary F h)).bits_mem_FP
      ((IntegralCriticalHistoryTask.get_binary P a .col).mod (dimension_binary F h)).bits_mem_FP)

noncomputable def program :=
  IntegralPowerProductBits.ProductStage.entryProgram (IntegralMonomialTermBits.family F)
    (IntegralCriticalFlatFactorQuery.writer P .factorPower)

noncomputable def controller := (program P F).controller.prepare (input P F)

include a h in
theorem controls : (program P F).Controls :=
  IntegralPowerProductBits.ProductStage.entry_controls _ (IntegralMonomialTermBits.familyAccess F h) _
    (IntegralCriticalFlatFactorQuery.writer_FP P a .factorPower)

include a h in
theorem certificates : (controller P F).Certificates (encQ := encBits) (encS := SingleCall.encState) :=
  (program P F).controller.prepare_certificates _ ((program P F).certificates (controls P a F h))
    (input_FP P a F h)

abbrev Replies (answer : List Bool → List Bool) : Prop :=
  ∀ c, MatrixProductBits.RecursiveStage.adjacent
      (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F)) (input P F c) →
    answer (IntegralCriticalFlatFactorQuery.writer P .factorPower
      (MatrixProductBits.factorQuery (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F))
        (input P F c))) =
      (IntegralPowerProductBits.powerFamily (IntegralMonomialTermBits.family F)).value
        (MatrixProductBits.factorQuery (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F))
          (input P F c))

include h in
theorem value (answer : List Bool → List Bool) (he : Replies P F answer) (c : List Bool) :
    (program P F).value answer (input P F c) =
      residueBits ((IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F)).power.matrix c
        (index P F .row c) (index P F .col c)) := by
  exact (MatrixProductBits.RecursiveStage.entry_value_at
    (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F))
    (IntegralPowerProductBits.productAccess (IntegralMonomialTermBits.family F)
      (IntegralMonomialTermBits.familyAccess F h))
    (IntegralCriticalFlatFactorQuery.writer P .factorPower) answer (input P F c) (he c)).trans
    (MatrixProductBits.powerEntry_packet
      (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F))
      (IntegralPowerProductBits.productAccess (IntegralMonomialTermBits.family F)
        (IntegralMonomialTermBits.familyAccess F h)) c (index P F .row c) (index P F .col c))

theorem halted_after (answer : List Bool → List Bool) (c : List Bool) :
    (controller P F).halted (((controller P F).reference answer)^[1]
      ((controller P F).initial c)) = true := by
  simpa only [controller, RecursiveController.Controller.prepare_halted_iterate, SingleCall.Program.controller] using
    (program P F).halted_after answer (input P F c)

include h in
theorem output_when_halted (answer : List Bool → List Bool) (he : Replies P F answer)
    (c : List Bool) (t : ℕ)
    (hh : (controller P F).halted (((controller P F).reference answer)^[t]
      ((controller P F).initial c)) = true) :
    (controller P F).output (((controller P F).reference answer)^[t]
      ((controller P F).initial c)) =
      residueBits ((IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F)).power.matrix c
        (index P F .row c) (index P F .col c)) := by
  simp only [controller, RecursiveController.Controller.prepare_halted_iterate, SingleCall.Program.controller] at hh
  simpa only [controller, RecursiveController.Controller.prepare_output_iterate, SingleCall.Program.controller] using
    ((program P F).output_when_halted answer (input P F c) t hh).trans (value P F h answer he c)

noncomputable def stateBound (c : List Bool) : ℕ :=
  2 * (input P F c).length + 4 + ((IntegralMonomialTermBits.family F).modulus c).size

theorem matrix_modulus (c : List Bool) :
    (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F)).power.modulus c =
      (IntegralMonomialTermBits.family F).modulus c := rfl

include a h in
theorem stateBound_unary : UnaryFn (stateBound P F) := by
  have HM : UnaryFn (fun c => ((IntegralMonomialTermBits.family F).modulus c).size) :=
    (UnaryFn.length (IntegralMonomialTermBits.familyAccess F h).modulus.bits_mem_FP).of_eq
      (fun _ => BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 2).mul (UnaryFn.length (input_FP P a F h))).add (UnaryFn.const 4)).add HM

include h in
theorem state_length (answer : List Bool → List Bool) (he : Replies P F answer) (c : List Bool) (t : ℕ) :
    (SingleCall.encState (((controller P F).reference answer)^[t]
      ((controller P F).initial c))).length ≤ stateBound P F c := by
  simp only [controller, RecursiveController.Controller.prepare_orbit, SingleCall.Program.controller]
  apply (program P F).state_length_of_bound answer (input P F c) t
    ((IntegralMonomialTermBits.family F).modulus c).size
  intro hr
  have HV := value P F h answer he c
  rw [SingleCall.Program.value, hr, ite_eq_left rfl] at HV
  have HQ : (program P F).finish = pairSnd := rfl
  rw [HQ, pairSnd_pair] at HV
  rw [HV]
  have : NeZero ((IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F)).power.modulus c) :=
    ⟨(IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F)).power.modulus_ne_zero c⟩
  rw [← BinaryNatCode.length_encode]
  apply ModularFold.bits_length_le
    (fun c => BinaryNatCode.encode ((IntegralMonomialTermBits.family F).modulus c)) c
  have HLT := ZMod.val_lt ((IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F)).power.matrix c
    (index P F .row c) (index P F .col c))
  have HLT' := HLT.trans_eq (matrix_modulus F c)
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using HLT'

theorem requests_in_bounds (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool)
    (hc : (controller P F).Requests answer budget c child) :
    ∃ s : Fin ((IntegralMonomialTermBits.family F).count c),
    ∃ r t : Fin ((IntegralMonomialTermBits.family F).rank c),
      child = IntegralCriticalFlatFactorQuery.writer P .factorPower (pair c
        (pair (BinaryNatCode.encode s.val) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) := by
  rw [controller, RecursiveController.Controller.prepare_requests_iff] at hc
  exact IntegralPowerProductBits.ProductStage.entry_requests_in_bounds (IntegralMonomialTermBits.family F)
    (IntegralCriticalFlatFactorQuery.writer P .factorPower) answer _ c child
    (index P F .row c) (index P F .col c) hc

theorem requests_rank (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .productEntry c)
    (hc : (controller P F).Requests answer budget c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨s, r, t, rfl⟩ := requests_in_bounds P F answer budget c child hc
  have HL := IntegralCriticalFlatFactorQuery.writer_lower_rank P .factorPower
    (pair c (pair (BinaryNatCode.encode s.val) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))
  simp only [pairFst_pair] at HL
  apply HL
  change IntegralCriticalHistoryTask.phase c = 5 at hp
  change 4 < IntegralCriticalHistoryTask.phase c
  omega

theorem requests_tasks (answer : List Bool → List Bool) (budget : List Bool → ℕ) (root c child : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P root c)
    (hc : (controller P F).Requests answer budget c child) :
    IntegralCriticalHistoryTask.Tasks P root child := by
  obtain ⟨s, r, t, rfl⟩ := requests_in_bounds P F answer budget c child hc
  apply IntegralCriticalFlatFactorQuery.writer_tasks
  simpa only [pairFst_pair] using ht

abbrev RepliesAt (answer : List Bool → List Bool) (c : List Bool) : Prop :=
   MatrixProductBits.RecursiveStage.adjacent
      (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F)) (input P F c) →
    answer (IntegralCriticalFlatFactorQuery.writer P .factorPower
      (MatrixProductBits.factorQuery (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F))
        (input P F c))) =
      (IntegralPowerProductBits.powerFamily (IntegralMonomialTermBits.family F)).value
        (MatrixProductBits.factorQuery (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F))
          (input P F c))

include h in
theorem value_at (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P F answer c) :
    (program P F).value answer (input P F c) =
      residueBits ((IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F)).power.matrix c
        (index P F .row c) (index P F .col c)) := by
  exact (MatrixProductBits.RecursiveStage.entry_value_at
    (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F))
    (IntegralPowerProductBits.productAccess (IntegralMonomialTermBits.family F)
      (IntegralMonomialTermBits.familyAccess F h))
    (IntegralCriticalFlatFactorQuery.writer P .factorPower) answer (input P F c) he).trans
    (MatrixProductBits.powerEntry_packet
      (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F))
      (IntegralPowerProductBits.productAccess (IntegralMonomialTermBits.family F)
        (IntegralMonomialTermBits.familyAccess F h)) c (index P F .row c) (index P F .col c))

include h in
theorem output_when_halted_at (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P F answer c)
    (t : ℕ)
    (hh : (controller P F).halted (((controller P F).reference answer)^[t]
      ((controller P F).initial c)) = true) :
    (controller P F).output (((controller P F).reference answer)^[t]
      ((controller P F).initial c)) =
      residueBits ((IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F)).power.matrix c
        (index P F .row c) (index P F .col c)) := by
  simp only [controller, RecursiveController.Controller.prepare_halted_iterate, SingleCall.Program.controller] at hh
  simpa only [controller, RecursiveController.Controller.prepare_output_iterate, SingleCall.Program.controller] using
    ((program P F).output_when_halted answer (input P F c) t hh).trans (value_at P F h answer c he)

include h in
theorem state_length_at (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P F answer c) (t : ℕ) :
    (SingleCall.encState (((controller P F).reference answer)^[t]
      ((controller P F).initial c))).length ≤ stateBound P F c := by
  simp only [controller, RecursiveController.Controller.prepare_orbit, SingleCall.Program.controller]
  apply (program P F).state_length_of_bound answer (input P F c) t
    ((IntegralMonomialTermBits.family F).modulus c).size
  intro hr
  have HV := value_at P F h answer c he
  rw [SingleCall.Program.value, hr, ite_eq_left rfl] at HV
  have HQ : (program P F).finish = pairSnd := rfl
  rw [HQ, pairSnd_pair] at HV
  rw [HV]
  have : NeZero ((IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F)).power.modulus c) :=
    ⟨(IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F)).power.modulus_ne_zero c⟩
  rw [← BinaryNatCode.length_encode]
  apply ModularFold.bits_length_le
    (fun c => BinaryNatCode.encode ((IntegralMonomialTermBits.family F).modulus c)) c
  have HLT := ZMod.val_lt ((IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family F)).power.matrix c
    (index P F .row c) (index P F .col c))
  have HLT' := HLT.trans_eq (matrix_modulus F c)
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using HLT'

end LeanCanny.Algebra.IntegralCriticalFlatGenericProductEntryBits

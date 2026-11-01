/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscMomentTypedRoutes
public import LeanCanny.Algebra.MatrixMomentEntryTypedReplies
/-! # Actual augmented PSC entries use the three native phase-zero routes -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits

noncomputable def momentEntryProgram (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : SingleCall.Program :=
  MatrixMoment.EntryBits.program
    (IntegralCriticalFlatMomentEntryBits.bits P a (characteristic P F) (characteristicAccess P a F h))
    (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F))
    (IntegralMixedPscMomentTasks.rowTask P (characteristic P F))
    (IntegralMixedPscMomentTasks.columnTask P (characteristic P F))
    (IntegralMixedPscMomentTasks.matrixTask P (characteristic P F))

theorem momentEntry_controls (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : (momentEntryProgram P a F h).Controls := by
  have HB : BinaryFn (fun q => (moment P F).dimension (pairFst q)) :=
    (momentAccess P a F h).dimension.comp pairFst_mem_FP
  have HD : (IntegralCriticalFlatMomentEntryBits.bits P a (characteristic P F) (characteristicAccess P a F h)).dimension ∈ FP := HB.bits_mem_FP
  exact MatrixMoment.EntryBits.program_controls _ HD _ _ _ _
    (IntegralCriticalFlatMomentEntryBits.input_FP P a (characteristic P F) (characteristicAccess P a F h))
    (IntegralMixedPscMomentTasks.rowTask_FP P a (characteristic P F) (characteristicAccess P a F h))
    (IntegralMixedPscMomentTasks.columnTask_FP P a (characteristic P F) (characteristicAccess P a F h))
    (IntegralMixedPscMomentTasks.matrixTask_FP P a (characteristic P F) (characteristicAccess P a F h))

abbrev MomentEntryRepliesAt (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  MatrixMoment.EntryBits.RepliesAt
    (IntegralCriticalFlatMomentEntryBits.bits P a (characteristic P F) (characteristicAccess P a F h))
    (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F))
    (IntegralMixedPscMomentTasks.rowTask P (characteristic P F))
    (IntegralMixedPscMomentTasks.columnTask P (characteristic P F))
    (IntegralMixedPscMomentTasks.matrixTask P (characteristic P F)) answer q

attribute [local irreducible] IntegralMixedPscCharacteristicBits.source characteristicAccess

theorem value1 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (answer : List Bool → List Bool) (q : List Bool) (he : MomentEntryRepliesAt P a F h answer q) :
    (momentEntryProgram P a F h).value answer q = momentEntry P F q := by
  rw [momentEntryProgram, MatrixMoment.EntryBits.program_value_local _ _ _ _ _ _ q he]
  let r : Fin (IntegralMixedPscMomentMatrix.size P F q) :=
    ⟨get P .row q % IntegralMixedPscMomentMatrix.size P F q, Nat.mod_lt _ (moment_size_pos P F q)⟩
  let t : Fin (IntegralMixedPscMomentMatrix.size P F q) :=
    ⟨get P .col q % IntegralMixedPscMomentMatrix.size P F q, Nat.mod_lt _ (moment_size_pos P F q)⟩
  have HE := IntegralBlockMomentBits.entry_correct (moment P F) (momentAccess P a F h) q r t
  have HM := congrArg (fun m => residueBits (((moment P F).powerMatrix q r t : ℤ) : ZMod m)) (moment_modulus P F q)
  exact HE.trans (HM.trans (IntegralMixedPscMomentMatrix.modularEntry_fin P F q r t).symm)

theorem action_replies1 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    MomentEntryRepliesAt P a F h (IntegralMixedPscMatrixModel.actionValue P F) q := by
  let r : Fin (IntegralMixedPscMomentMatrix.size P F q) :=
    ⟨get P .row q % IntegralMixedPscMomentMatrix.size P F q, Nat.mod_lt _ (moment_size_pos P F q)⟩
  let t : Fin (IntegralMixedPscMomentMatrix.size P F q) :=
    ⟨get P .col q % IntegralMixedPscMomentMatrix.size P F q, Nat.mod_lt _ (moment_size_pos P F q)⟩
  have HI : IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) q =
      pair (IntegralBlockMomentBits.context q r.modNat.val t.modNat.val)
        (pair (BinaryNatCode.encode r.divNat.val) (BinaryNatCode.encode t.divNat.val)) :=
    IntegralBlockMomentBits.outer_packet (moment P F) q r t
  have HD : (IntegralCriticalFlatMomentEntryBits.bits P a (characteristic P F) (characteristicAccess P a F h)).dimension
      (IntegralBlockMomentBits.context q r.modNat.val t.modNat.val) =
      BinaryNatCode.encode ((moment P F).dimension q) := by
    simp only [IntegralCriticalFlatMomentEntryBits.bits, IntegralBlockMomentBits.bitsAccess,
      IntegralBlockMomentBits.context, pairFst_pair]
  exact MatrixMoment.EntryBits.repliesAt_of_typed _ _ _ _ _ _ q
    (IntegralBlockMomentBits.context q r.modNat.val t.modNat.val) ((moment P F).dimension q) r.divNat t.divNat HD HI
    (fun i => rowTask_value P a F h g q hv i r.modNat t.modNat)
    (fun i => columnTask_value P a F h g q hv i r.modNat t.modNat)
    (fun i j => matrixTask_value P a F h g q hv i j r.modNat t.modNat)

end LeanCanny.Algebra.IntegralMixedPscUpperBits

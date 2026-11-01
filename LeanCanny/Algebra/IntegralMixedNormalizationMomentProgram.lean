/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationMomentTypedRoutes
public import LeanCanny.Algebra.MatrixMomentEntryTypedReplies
/-! # The actual normalization augmented-entry selector -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false

noncomputable def momentEntryProgram (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : SingleCall.Program :=
  MatrixMoment.EntryBits.program
    (IntegralCriticalFlatMomentEntryBits.bits P a (source P F) (access P a F h))
    (IntegralCriticalFlatMomentEntryBits.input P (source P F))
    (IntegralMixedNormalizationMomentTasks.rowTask P (source P F))
    (IntegralMixedNormalizationMomentTasks.columnTask P (source P F))
    (IntegralMixedNormalizationMomentTasks.matrixTask P (source P F))

theorem momentEntry_controls (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : (momentEntryProgram P a F h).Controls := by
  have HB : BinaryFn (fun q => (moment P F).dimension (pairFst q)) :=
    (momentAccess P a F h).dimension.comp pairFst_mem_FP
  have HD : (IntegralCriticalFlatMomentEntryBits.bits P a (source P F) (access P a F h)).dimension ∈ FP := HB.bits_mem_FP
  exact MatrixMoment.EntryBits.program_controls _ HD _ _ _ _
    (IntegralCriticalFlatMomentEntryBits.input_FP P a (source P F) (access P a F h))
    (IntegralMixedNormalizationMomentTasks.rowTask_FP P a (source P F) (access P a F h))
    (IntegralMixedNormalizationMomentTasks.columnTask_FP P a (source P F) (access P a F h))
    (IntegralMixedNormalizationMomentTasks.matrixTask_FP P a (source P F) (access P a F h))

abbrev MomentEntryRepliesAt (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  MatrixMoment.EntryBits.RepliesAt
    (IntegralCriticalFlatMomentEntryBits.bits P a (source P F) (access P a F h))
    (IntegralCriticalFlatMomentEntryBits.input P (source P F))
    (IntegralMixedNormalizationMomentTasks.rowTask P (source P F))
    (IntegralMixedNormalizationMomentTasks.columnTask P (source P F))
    (IntegralMixedNormalizationMomentTasks.matrixTask P (source P F)) answer q

attribute [local irreducible] source access

theorem value3 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (answer : List Bool → List Bool) (q : List Bool) (he : MomentEntryRepliesAt P a F h answer q) :
    (momentEntryProgram P a F h).value answer q = momentEntry P F q := by
  rw [momentEntryProgram, MatrixMoment.EntryBits.program_value_local _ _ _ _ _ _ q he]
  let r : Fin (IntegralMixedNormalizationMomentMatrixBits.size P F q) :=
    ⟨get P .row q % IntegralMixedNormalizationMomentMatrixBits.size P F q, Nat.mod_lt _ (moment_size_pos P F q)⟩
  let t : Fin (IntegralMixedNormalizationMomentMatrixBits.size P F q) :=
    ⟨get P .col q % IntegralMixedNormalizationMomentMatrixBits.size P F q, Nat.mod_lt _ (moment_size_pos P F q)⟩
  have HE := IntegralBlockMomentBits.entry_correct (moment P F) (momentAccess P a F h) q r t
  have HM := congrArg (fun m => residueBits (((moment P F).powerMatrix q r t : ℤ) : ZMod m)) (moment_modulus P F q)
  exact HE.trans (HM.trans (IntegralMixedNormalizationMomentMatrixBits.modularEntry_fin P F q r t).symm)

theorem top_replies3 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    MomentEntryRepliesAt P a F h (value P F) q := by
  let r : Fin (IntegralMixedNormalizationMomentMatrixBits.size P F q) :=
    ⟨get P .row q % IntegralMixedNormalizationMomentMatrixBits.size P F q, Nat.mod_lt _ (moment_size_pos P F q)⟩
  let t : Fin (IntegralMixedNormalizationMomentMatrixBits.size P F q) :=
    ⟨get P .col q % IntegralMixedNormalizationMomentMatrixBits.size P F q, Nat.mod_lt _ (moment_size_pos P F q)⟩
  have HI : IntegralCriticalFlatMomentEntryBits.input P (source P F) q =
      pair (IntegralBlockMomentBits.context q r.modNat.val t.modNat.val)
        (pair (BinaryNatCode.encode r.divNat.val) (BinaryNatCode.encode t.divNat.val)) :=
    IntegralBlockMomentBits.outer_packet (moment P F) q r t
  have HD : (IntegralCriticalFlatMomentEntryBits.bits P a (source P F) (access P a F h)).dimension
      (IntegralBlockMomentBits.context q r.modNat.val t.modNat.val) =
      BinaryNatCode.encode ((moment P F).dimension q) := by
    simp only [IntegralCriticalFlatMomentEntryBits.bits, IntegralBlockMomentBits.bitsAccess,
      IntegralBlockMomentBits.context, pairFst_pair]
  exact MatrixMoment.EntryBits.repliesAt_of_typed _ _ _ _ _ _ q
    (IntegralBlockMomentBits.context q r.modNat.val t.modNat.val) ((moment P F).dimension q) r.divNat t.divNat HD HI
    (fun i => rowTask_value P a F h g q hv i r.modNat t.modNat)
    (fun i => columnTask_value P a F h g q hv i r.modNat t.modNat)
    (fun i j => matrixTask_value P a F h g q hv i j r.modNat t.modNat)

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits

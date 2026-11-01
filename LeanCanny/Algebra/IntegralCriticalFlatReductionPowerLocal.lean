/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatReductionPower
public import LeanCanny.Algebra.IntegralBlockPowerRecursiveStageLocal
/-! # Flat reduction powering with replies confined to the current source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatReductionPowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

abbrev RepliesAt (P : Parameters) (S : Source) (answer : List Bool → List Bool) (c : List Bool) : Prop :=
  IntegralBlockPowerBits.RecursiveStage.RepliesAt (family P S)
    (IntegralCriticalFlatMatrixQuery.writer P .reductionEntry) answer c

theorem halted_after_local (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S)
    (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) :
    (controller P a S h n).halted (((controller P a S h n).reference answer)^[clock P S c]
      ((controller P a S h n).initial c)) = true :=
  IntegralBlockPowerBits.RecursiveStage.halted_after_local (family P S) (access P a S h n) _ answer c he

theorem output_when_halted_local (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S)
    (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) (t : ℕ)
    (hh : (controller P a S h n).halted (((controller P a S h n).reference answer)^[t]
      ((controller P a S h n).initial c)) = true) :
    (controller P a S h n).output (((controller P a S h n).reference answer)^[t]
      ((controller P a S h n).initial c)) =
      (IntegralReductionActionBits.powerFamily S).value (IntegralCriticalFlatActionBits.packet P S c) :=
  (IntegralBlockPowerBits.RecursiveStage.output_when_halted_local (family P S) (access P a S h n) _ answer c he t hh).trans
    (IntegralBlockPowerBits.Family.requery_value _ _ c)

theorem state_length_local (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S)
    (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) (t : ℕ) :
    (((controller P a S h n).reference answer)^[t] ((controller P a S h n).initial c)).length ≤ stateBound P S c :=
  IntegralBlockPowerBits.RecursiveStage.state_length_local (family P S) (access P a S h n) _ answer c he t

theorem requests_frame_local (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S)
    (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c)
    (budget : List Bool → ℕ) (child : List Bool) (hp : isPhase .reductionPower c)
    (hc : (controller P a S h n).Requests answer budget c child) :
    RankedHistoryTask.root child = RankedHistoryTask.root c ∧ child.length ≤ wordBudget P c ∧ rank P child < rank P c := by
  obtain ⟨i, j, rfl⟩ := IntegralBlockPowerBits.RecursiveStage.requests_in_bounds_local
    (family P S) (access P a S h n) (IntegralCriticalFlatMatrixQuery.writer P .reductionEntry) answer c he budget child hc
  refine ⟨?_, ?_, ?_⟩
  · simpa only [pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_root P .reductionEntry
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  · simpa only [pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_length P .reductionEntry
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  · have H := IntegralCriticalFlatMatrixQuery.writer_lower_rank P .reductionEntry
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
    simp only [pairFst_pair] at H
    apply H
    change phase c = 18 at hp
    change 17 < phase c
    omega

end LeanCanny.Algebra.IntegralCriticalFlatReductionPowerBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualReductionEntry
/-! # Actual finite reduction-power requests retain the reduction matrix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualReductionPowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalFlatReductionPowerBits
set_option backward.isDefEq.respectTransparency false

private theorem original_packet (P : Parameters) (S : Source) (c : List Bool) :
    IntegralBerkowitzBlockBits.original (IntegralCriticalFlatActionBits.packet P S c) = c :=
  IntegralCriticalFlatRelativeFactorBits.outer_original P S.toSource c

theorem family_dimension (P : Parameters) (S : Source) (c : List Bool) :
    (family P S).dimension c = S.dimension c := by
  change S.dimension (IntegralBerkowitzBlockBits.original (IntegralCriticalFlatActionBits.packet P S c)) = _
  rw [original_packet]

theorem family_rank (P : Parameters) (S : Source) (c : List Bool) :
    (family P S).rank c = S.rank c := by
  change S.rank (IntegralBerkowitzBlockBits.original (IntegralCriticalFlatActionBits.packet P S c)) = _
  rw [original_packet]

theorem family_modulus (P : Parameters) (S : Source) (c : List Bool) :
    (family P S).modulus c = S.modulus c := by
  change S.modulus (IntegralBerkowitzBlockBits.original (IntegralCriticalFlatActionBits.packet P S c)) = _
  rw [original_packet]

theorem integerEntry_family (P : Parameters) (S : Source) (c : List Bool) (r t : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry ((family P S).powerMatrix c) r t =
      IntegralCriticalTotalSnapshotBits.integerEntry (IntegralCriticalTotalSnapshotBits.blockMatrix S.toSource c) r t := by
  change IntegralCriticalTotalSnapshotBits.integerEntry
    (IntegralCriticalTotalSnapshotBits.blockMatrix S.toSource
      (IntegralBerkowitzBlockBits.original (IntegralCriticalFlatActionBits.packet P S c))) r t = _
  rw [original_packet]

private theorem reduction_modulus (F : Scripts) (c : List Bool) :
    (reduction F).modulus c = IntegralCriticalHistoryTask.modulus F.toParameters c := rfl

attribute [local irreducible] relative reduction characteristic

theorem replies (F : Scripts) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c) :
    RepliesAt F.toParameters (reduction F) (IntegralCriticalFlatActualReductionEntryBits.value F) c := by
  intro i j
  let r : Fin ((reduction F).dimension c * (reduction F).rank c) :=
    ⟨i.val, by simpa only [family_dimension, family_rank] using i.isLt⟩
  let t : Fin ((reduction F).dimension c * (reduction F).rank c) :=
    ⟨j.val, by simpa only [family_dimension, family_rank] using j.isLt⟩
  have HV := IntegralCriticalFlatActualReductionEntryBits.child_value F c hv r t
  have HE : (family F.toParameters (reduction F)).powerMatrix c i j =
      IntegralCriticalTotalSnapshotBits.blockMatrix (reduction F).toSource c r t :=
    (IntegralCriticalTotalSnapshotBits.integerEntry_fin _ i j).symm.trans
      ((integerEntry_family F.toParameters (reduction F) c i.val j.val).trans
        (IntegralCriticalTotalSnapshotBits.integerEntry_fin _ r t))
  have HM : (family F.toParameters (reduction F)).modulus c = IntegralCriticalHistoryTask.modulus F.toParameters c :=
    (family_modulus F.toParameters (reduction F) c).trans (reduction_modulus F c)
  rw [HE]
  exact HV.trans (congrArg (fun m : ℕ => residueBits
    ((IntegralCriticalTotalSnapshotBits.blockMatrix (reduction F).toSource c r t : ℤ) : ZMod m)) HM.symm)

end LeanCanny.Algebra.IntegralCriticalFlatActualReductionPowerBits

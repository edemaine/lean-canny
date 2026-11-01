/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualMomentChild
public import LeanCanny.Algebra.IntegralCriticalFlatActualRelativeEntry
/-! # Actual relative factor values from their selected flattened children -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualRelativeFactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] characteristic characteristicAccess IntegralCriticalTotalCreatingBits.atFamily
  IntegralCriticalTotalSnapshotBits.modularPowerEntry IntegralCriticalTotalSnapshotBits.powerEntry

noncomputable def value (F : Scripts) (c : List Bool) : List Bool :=
  IntegralCriticalTotalSnapshotBits.modularPowerEntry F c (get F.toParameters .row c) (get F.toParameters .col c)

noncomputable def outer (F : Scripts) (c : List Bool) : List Bool :=
  outerPacket (characteristic F) (IntegralCriticalFlatRelativeFactorBits.packet F.toParameters c)

noncomputable def diagonalChild (F : Scripts) (c : List Bool) : List Bool :=
  IntegralCriticalFlatBerkowitzQuery.entryWriter F.toParameters (characteristic F) (diagonalQuery (characteristic F) (outer F c))

noncomputable def momentChild (F : Scripts) (c : List Bool) : List Bool :=
  IntegralCriticalFlatBerkowitzQuery.momentWriter F.toParameters (outer F c)

theorem outer_parent (F : Scripts) (c : List Bool) : original (outer F c) = c :=
  IntegralCriticalFlatRelativeFactorBits.outer_original _ _ _

theorem program_value_finite (F : Scripts) (h : Controls F) (answer : List Bool → List Bool) (c : List Bool)
    (hv : IntegralCriticalTotalCompanionBits.valid F c)
    (hd : selector (characteristic F) (outer F c) = [false, true] →
      answer (diagonalChild F c) = IntegralCriticalFlatActualActionBits.value F (diagonalChild F c))
    (hm : selector (characteristic F) (outer F c) = [true, true] →
      answer (momentChild F c) = IntegralCriticalTotalMomentValueSnapshotBits.value F (momentChild F c))
    (i j : Fin (powerDimension (characteristic F) c))
    (hi : get F.toParameters .row c = i.val) (hj : get F.toParameters .col c = j.val) :
    (IntegralCriticalFlatRelativeFactorBits.program F.toParameters (characteristic F)).value answer c = value F c := by
  have HP : IntegralCriticalTotalCompanionBits.valid F (original (outer F c)) := by rw [outer_parent]; exact hv
  have HE := IntegralCriticalFlatRelativeFactorBits.value_at F.toParameters (characteristic F) (characteristicAccess F h) answer c
    (fun hg => (hd hg).trans (IntegralCriticalFlatActualDiagonalBits.child_value F h (outer F c) HP hg))
    (fun hg => (hm hg).trans (IntegralCriticalFlatActualMomentChildBits.child_value F c hv))
  have HC : entryProgram (characteristic F) (characteristicAccess F h)
      (IntegralCriticalFlatRelativeFactorBits.packet F.toParameters c) =
      residueBits (((characteristic F).powerMatrix c i j : ℤ) : ZMod ((characteristic F).modulus c)) := by
    rw [IntegralCriticalFlatRelativeFactorBits.packet, hi, hj]
    exact entry_correct _ _ c i j
  have HM := congrArg (fun m : ℕ => residueBits (((characteristic F).powerMatrix c i j : ℤ) : ZMod m))
    (characteristic_modulus F c)
  rw [value, hi, hj]
  exact HE.trans (HC.trans (HM.trans (IntegralCriticalTotalSnapshotBits.modularPowerEntry_fin F c i j).symm))

theorem momentChild_valid (F : Scripts) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c) :
    IntegralCriticalTotalCompanionBits.valid F (momentChild F c) := by
  change birth F.toParameters (momentChild F c) < (F.rules (RankedHistoryTask.root (momentChild F c))).length
  have HR := IntegralCriticalFlatBerkowitzQuery.momentWriter_root F.toParameters (outer F c)
  have HB := IntegralCriticalFlatBerkowitzQuery.momentWriter_birth F.toParameters (outer F c)
  rw [outer_parent] at HR HB
  change RankedHistoryTask.root (momentChild F c) = RankedHistoryTask.root c at HR
  change birth F.toParameters (momentChild F c) = birth F.toParameters c at HB
  rw [HR, HB]
  exact hv

theorem diagonalChild_valid (F : Scripts) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c) :
    IntegralCriticalTotalCompanionBits.valid F (diagonalChild F c) := by
  let p := diagonalQuery (characteristic F) (outer F c)
  have HP : original p = c := (IntegralCriticalFlatRelativeFactorBits.diagonal_original _ _).trans (outer_parent F c)
  have HR := IntegralCriticalFlatBerkowitzQuery.entryWriter_root F.toParameters (characteristic F) p
  rw [HP] at HR
  change RankedHistoryTask.root (diagonalChild F c) = RankedHistoryTask.root c at HR
  have HB : birth F.toParameters (diagonalChild F c) = birth F.toParameters c := by
    change birth F.toParameters (IntegralCriticalFlatMatrixQuery.writer F.toParameters .actionEntry
      (IntegralCriticalFlatBerkowitzQuery.entryPacket (characteristic F) p)) = _
    rw [IntegralCriticalFlatMatrixQuery.writer_birth, IntegralCriticalFlatBerkowitzQuery.entry_parent, HP]
  change birth F.toParameters (diagonalChild F c) < (F.rules (RankedHistoryTask.root (diagonalChild F c))).length
  rw [HR, HB]
  exact hv

end LeanCanny.Algebra.IntegralCriticalFlatActualRelativeFactorBits

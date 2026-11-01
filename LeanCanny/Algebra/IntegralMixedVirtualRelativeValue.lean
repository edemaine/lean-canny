/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualRelativeChildren
public import LeanCanny.Algebra.IntegralMixedVirtualRelativeModel
public import LeanCanny.Algebra.IntegralCriticalFlatRelativeFactorLocal
/-! # Actual virtual relative factors from their selected matrix children -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
theorem characteristic_task_modulus (P : Parameters) (F : Family) (q : List Bool) :
    (characteristic P F).modulus q = modulus P q := rfl
attribute [local irreducible] characteristic characteristicAccess

noncomputable def outer23 (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  outerPacket (characteristic P F) (IntegralCriticalFlatRelativeFactorBits.packet P q)
noncomputable def diagonalChild23 (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  IntegralCriticalFlatBerkowitzQuery.entryWriter P (characteristic P F) (diagonalQuery (characteristic P F) (outer23 P F q))
noncomputable def momentChild23 (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  IntegralCriticalFlatBerkowitzQuery.momentWriter P (outer23 P F q)

theorem outer23_parent (P : Parameters) (F : Family) (q : List Bool) : original (outer23 P F q) = q :=
  IntegralCriticalFlatRelativeFactorBits.outer_original _ _ _

theorem value23 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q)
    (hd : selector (characteristic P F) (outer23 P F q) = [false, true] →
      answer (diagonalChild23 P F q) = IntegralMixedVirtualMatrixBits.actionEntry P F (diagonalChild23 P F q))
    (hm : selector (characteristic P F) (outer23 P F q) = [true, true] →
      answer (momentChild23 P F q) = momentValue P F (momentChild23 P F q))
    (i j : Fin (powerDimension (characteristic P F) q)) (hi : get P .row q = i.val) (hj : get P .col q = j.val) :
    (IntegralCriticalFlatRelativeFactorBits.program P (characteristic P F)).value answer q =
      IntegralMixedVirtualMatrixBits.relativeFactor P F q := by
  have HP : IntegralMixedVirtualCaps.valid P (original (outer23 P F q)) := by rw [outer23_parent]; exact hv
  have HE := IntegralCriticalFlatRelativeFactorBits.value_at P (characteristic P F) (characteristicAccess P a F h) answer q
    (fun hg => (hd hg).trans (diagonal_child P a F h g (outer23 P F q) HP hg))
    (fun hg => (hm hg).trans (relative_moment_child P F g q hv))
  have HC : entryProgram (characteristic P F) (characteristicAccess P a F h)
      (IntegralCriticalFlatRelativeFactorBits.packet P q) =
      residueBits (((characteristic P F).powerMatrix q i j : ℤ) : ZMod ((characteristic P F).modulus q)) := by
    rw [IntegralCriticalFlatRelativeFactorBits.packet, hi, hj]
    exact entry_correct _ _ q i j
  have HF : IntegralMixedVirtualMatrixBits.relativeFactor P F q =
      residueBits (((characteristic P F).powerMatrix q i j : ℤ) : ZMod (modulus P q)) := by
    unfold IntegralMixedVirtualMatrixBits.relativeFactor
    rw [IntegralMixedVirtualMatrixBits.power_snapshot, hi, hj, IntegralCriticalTotalSnapshotBits.integerEntry_fin]
  have HM := congrArg (fun m => residueBits (((characteristic P F).powerMatrix q i j : ℤ) : ZMod m))
    (characteristic_task_modulus P F q)
  exact HE.trans (HC.trans (HM.trans HF.symm))

end LeanCanny.Algebra.IntegralMixedVirtualUpperBits

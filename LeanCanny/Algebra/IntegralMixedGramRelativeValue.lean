/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramRelativeChildren
public import LeanCanny.Algebra.IntegralMixedGramRelativeModel
public import LeanCanny.Algebra.IntegralCriticalFlatRelativeFactorLocal
/-! # Actual virtual relative factors from their selected matrix children -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
theorem characteristic_task_modulus (P : Parameters) (F : Family) (q : List Bool) :
    (characteristic P F).modulus q = modulus P q := IntegralMixedGramCharacteristicSource.source_modulus P F q
attribute [local irreducible] IntegralMixedGramCharacteristicSource.source characteristicAccess

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
      answer (diagonalChild23 P F q) = IntegralMixedGramMatrixModel.actionValue P F (diagonalChild23 P F q))
    (hm : selector (characteristic P F) (outer23 P F q) = [true, true] →
      answer (momentChild23 P F q) = momentValue P F (momentChild23 P F q))
    (i j : Fin (powerDimension (characteristic P F) q)) (hi : get P .row q = i.val) (hj : get P .col q = j.val) :
    (IntegralCriticalFlatRelativeFactorBits.program P (characteristic P F)).value answer q =
      IntegralMixedGramMatrixModel.factorValue P F q := by
  have HP : IntegralMixedVirtualCaps.valid P (original (outer23 P F q)) := by rw [outer23_parent]; exact hv
  have HE := IntegralCriticalFlatRelativeFactorBits.value_at P (characteristic P F) (characteristicAccess P a F h) answer q
    (fun hg => (hd hg).trans (diagonal_child P a F h g (outer23 P F q) HP hg))
    (fun hg => (hm hg).trans (relative_moment_child P F g q hv))
  have HC : entryProgram (characteristic P F) (characteristicAccess P a F h)
      (IntegralCriticalFlatRelativeFactorBits.packet P q) =
      residueBits (((characteristic P F).powerMatrix q i j : ℤ) : ZMod ((characteristic P F).modulus q)) := by
    rw [IntegralCriticalFlatRelativeFactorBits.packet, hi, hj]
    exact entry_correct _ _ q i j
  have HF : IntegralMixedGramMatrixModel.factorValue P F q =
      residueBits (((characteristic P F).powerMatrix q i j : ℤ) : ZMod (modulus P q)) := by
    unfold IntegralMixedGramMatrixModel.factorValue
    rw [IntegralMixedGramMatrixModel.power_snapshot, hi, hj]
    exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
      (IntegralCriticalTotalSnapshotBits.integerEntry_fin ((characteristic P F).powerMatrix q) i j)
  have HM := congrArg (fun m => residueBits (((characteristic P F).powerMatrix q i j : ℤ) : ZMod m))
    (characteristic_task_modulus P F q)
  exact HE.trans (HC.trans (HM.trans HF.symm))

end LeanCanny.Algebra.IntegralMixedGramUpperBits

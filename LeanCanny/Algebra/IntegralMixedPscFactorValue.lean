/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscMomentQuery
public import LeanCanny.Algebra.IntegralMixedPscMomentRoutes
public import LeanCanny.Algebra.IntegralBerkowitzBlockControllerLocal
public import LeanCanny.Computation.SingleCallRequery
/-! # Actual PSC characteristic factors use only phase-zero and phase-two children -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits

noncomputable def factorValue (P : Parameters) (F : Family) := IntegralMixedPscMatrixModel.factorValue P F

noncomputable def factorProgram (P : Parameters) (F : Family) :=
  (entryController (characteristic P F) (IntegralMixedPscMomentTasks.entryWriter P (characteristic P F)) (momentTask P)).requery
    (IntegralCriticalFlatRelativeFactorBits.packet P)

theorem factor_controls (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (factorProgram P F).Controls :=
  SingleCall.Program.requery_controls _
    (entryController_controls (characteristic P F) (characteristicAccess P a F h) _ _ (IntegralMixedPscMomentTasks.entryWriter_FP P a (characteristic P F) (characteristicAccess P a F h)) (momentTask_FP P a))
    _ (IntegralCriticalFlatRelativeFactorBits.packet_FP P a)

theorem diagonal_value (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (original z)) (hd : selector (characteristic P F) z = [false, true]) :
    IntegralMixedPscMatrixModel.actionValue P F (IntegralMixedPscMomentTasks.entryWriter P (characteristic P F) (diagonalQuery (characteristic P F) z)) = (characteristicAccess P a F h).entry (diagonalQuery (characteristic P F) z) := by
  have HS : stage (characteristic P F) z < (characteristic P F).dimension (original z) :=
    ((Berkowitz.QueryBits.select_diagonal_iff _ _ _ _ _).mp ((selector_eq _ _).symm.trans hd)).2.1
  let i : Fin ((characteristic P F).dimension (original z)) := ⟨_, HS⟩
  let r := basisIndex (characteristic P F) basisRowCode z
  let t := basisIndex (characteristic P F) basisColCode z
  exact (actionChild_value P F g (original z) hv i i r t).trans
    ((characteristicAccess P a F h).entry_eq (original z) i i r t).symm

noncomputable def outer (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  outerPacket (characteristic P F) (IntegralCriticalFlatRelativeFactorBits.packet P q)
noncomputable def diagonalChild (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  IntegralMixedPscMomentTasks.entryWriter P (characteristic P F) (diagonalQuery (characteristic P F) (outer P F q))
noncomputable def momentChild (P : Parameters) (F : Family) (q : List Bool) : List Bool := momentTask P (outer P F q)

theorem outer_parent (P : Parameters) (F : Family) (q : List Bool) : original (outer P F q) = q :=
  IntegralCriticalFlatRelativeFactorBits.outer_original _ _ _

theorem factor_value_at (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q)
    (hd : selector (characteristic P F) (outer P F q) = [false, true] →
      answer (diagonalChild P F q) = IntegralMixedPscMatrixModel.actionValue P F (diagonalChild P F q))
    (hm : selector (characteristic P F) (outer P F q) = [true, true] →
      answer (momentChild P F q) = momentValue P F (momentChild P F q))
    (i j : Fin (powerDimension (characteristic P F) q)) (hi : get P .row q = i.val) (hj : get P .col q = j.val) :
    (factorProgram P F).value answer q = factorValue P F q := by
  have HP : IntegralMixedVirtualCaps.valid P (original (outer P F q)) := by rw [outer_parent]; exact hv
  have HE : (factorProgram P F).value answer q =
      entryProgram (characteristic P F) (characteristicAccess P a F h) (IntegralCriticalFlatRelativeFactorBits.packet P q) := by
    rw [factorProgram, SingleCall.Program.requery_value]
    exact entryController_value_at (characteristic P F) (characteristicAccess P a F h) _ _ answer _
      (fun hg => (hd hg).trans (diagonal_value P a F h g (outer P F q) HP hg))
      (fun hg => (hm hg).trans (relative_moment_child P F q))
  have HC : entryProgram (characteristic P F) (characteristicAccess P a F h) (IntegralCriticalFlatRelativeFactorBits.packet P q) =
      residueBits (((characteristic P F).powerMatrix q i j : ℤ) : ZMod ((characteristic P F).modulus q)) := by
    rw [IntegralCriticalFlatRelativeFactorBits.packet, hi, hj]
    exact entry_correct _ _ q i j
  have HF : factorValue P F q = residueBits (((characteristic P F).powerMatrix q i j : ℤ) : ZMod (modulus P q)) := by
    unfold factorValue IntegralMixedPscMatrixModel.factorValue
    rw [IntegralMixedPscMatrixModel.power_snapshot, hi, hj]
    exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
      (IntegralCriticalTotalSnapshotBits.integerEntry_fin ((characteristic P F).powerMatrix q) i j)
  exact HE.trans (HC.trans HF.symm)

end LeanCanny.Algebra.IntegralMixedPscUpperBits

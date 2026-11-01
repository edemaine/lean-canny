/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeUpperMachines
/-! # Upper native replies are the actual current creating-source values -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relative relativeAccess reduction reductionAccess characteristic characteristicAccess
  IntegralCriticalTotalCreatingBits.atFamily

theorem next_valid (F : Scripts) (p : Phase) (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    IntegralCriticalTotalCompanionBits.valid F (IntegralCriticalFlatEulerBits.next F.toParameters p q) := by
  change birth F.toParameters (IntegralCriticalFlatEulerBits.next F.toParameters p q) <
    (F.rules (RankedHistoryTask.root (IntegralCriticalFlatEulerBits.next F.toParameters p q))).length
  rw [IntegralCriticalFlatEulerBits.next_birth, IntegralCriticalFlatEulerBits.next_root]
  exact hv

theorem matrix_valid (F : Scripts) (p : Phase) (q : List Bool) (i j : ℕ)
    (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    IntegralCriticalTotalCompanionBits.valid F (IntegralCriticalFlatMatrixQuery.writer F.toParameters p
      (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j)))) := by
  change birth F.toParameters _ < (F.rules (RankedHistoryTask.root _)).length
  rw [IntegralCriticalFlatMatrixQuery.writer_birth, IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair]
  exact hv

theorem matrix_phase (F : Scripts) (p : Phase) (q : List Bool) (i j : ℕ) :
    isPhase p (IntegralCriticalFlatMatrixQuery.writer F.toParameters p
      (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j)))) :=
  IntegralCriticalFlatMatrixQuery.writer_phase _ _ _

theorem replies18 (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    IntegralCriticalFlatReductionPowerBits.RepliesAt F.toParameters (reduction F) (answer F x) q := by
  intro i j
  exact (hx.reductionEntry _ (matrix_valid F .reductionEntry q i.val j.val hv)
    (matrix_phase F .reductionEntry q i.val j.val)).trans
    (IntegralCriticalFlatActualReductionPowerBits.replies F q hv i j)

theorem replies22 (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    IntegralCriticalFlatMomentBits.RepliesAt F.toParameters (characteristic F) (answer F x) q := by
  intro i j
  exact (hx.momentEntry _ (matrix_valid F .momentEntry q i.val j.val hv)
    (matrix_phase F .momentEntry q i.val j.val)).trans (IntegralCriticalFlatActualMomentBits.replies F q hv i j)

theorem replies24 (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    IntegralCriticalFlatActualRelativeBits.RepliesAt F (answer F x) q := by
  intro i j
  exact (hx.relativeFactor _ (matrix_valid F .relativeFactor q i.val j.val hv)
    (matrix_phase F .relativeFactor q i.val j.val)).trans (IntegralCriticalFlatActualRawRelativeEntryBits.replies F q hv i j)

theorem diagonal_phase (F : Scripts) (q : List Bool) :
    isPhase .actionEntry (IntegralCriticalFlatActualRelativeFactorBits.diagonalChild F q) := by
  change phase (IntegralCriticalFlatMatrixQuery.writer F.toParameters .actionEntry
    (IntegralCriticalFlatBerkowitzQuery.entryPacket (characteristic F)
      (IntegralBerkowitzBlockBits.diagonalQuery (characteristic F) (IntegralCriticalFlatActualRelativeFactorBits.outer F q)))) = _
  exact IntegralCriticalFlatMatrixQuery.writer_phase _ _ _

theorem moment_phase (F : Scripts) (q : List Bool) :
    isPhase .momentPower (IntegralCriticalFlatActualRelativeFactorBits.momentChild F q) :=
  IntegralCriticalFlatBerkowitzQuery.momentWriter_phase _ _

theorem value17 (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) (hf : finiteAxes F (reductionSize F) q) :
    (IntegralCriticalFlatReductionEntryBits.program F.toParameters (relative F) (relativeAccess F h)).value (answer F x) q =
      IntegralCriticalFlatActualReductionEntryBits.value F q := by
  exact IntegralCriticalFlatActualLowerChildBits.program_value_finite F h _ q hv
    (fun _ => hx.lower _ (IntegralCriticalFlatActualLowerChildBits.child_valid F q hv)
      (IntegralCriticalFlatActualLowerChildBits.child_phase F q)) ⟨_, hf.1⟩ ⟨_, hf.2⟩ rfl rfl

theorem value19 (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) (hf : finiteAxes F (reductionSize F) q) :
    (IntegralCriticalFlatActionBits.program F.toParameters (reduction F)).value (answer F x) q =
      IntegralCriticalFlatActualActionBits.value F q := by
  apply IntegralCriticalFlatActualActionBits.program_value_finite F _ q ?_ ⟨_, hf.1⟩ ⟨_, hf.2⟩ rfl rfl
  intro _
  exact (hx.reductionPower _ (next_valid F .reductionPower q hv) (IntegralCriticalFlatEulerBits.next_phase _ _ _)).trans
    (IntegralCriticalTotalActionSnapshotBits.power_next F .reductionPower q)

theorem value23 (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) (hf : finiteAxes F (factorSize F) q) :
    (IntegralCriticalFlatRelativeFactorBits.program F.toParameters (characteristic F)).value (answer F x) q =
      IntegralCriticalFlatActualRelativeFactorBits.value F q :=
  IntegralCriticalFlatActualRelativeFactorBits.program_value_finite F h _ q hv
    (fun _ => hx.action _ (IntegralCriticalFlatActualRelativeFactorBits.diagonalChild_valid F q hv) (diagonal_phase F q))
    (fun _ => hx.moment _ (IntegralCriticalFlatActualRelativeFactorBits.momentChild_valid F q hv) (moment_phase F q))
    ⟨_, hf.1⟩ ⟨_, hf.2⟩ rfl rfl

end LeanCanny.Algebra.IntegralCriticalNativeUpperBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscNativeMomentEntry
/-! # Native PSC moment powering uses current finite phase-one entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch

abbrev MomentEntryMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, selected P F .derivativeCoefficient q = true → answer q = entryValue P F q

abbrev MomentRepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i j : Fin (IntegralMixedPscMomentMatrix.size P F q),
    answer (IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((moment P F).powerMatrix q i j : ℤ) : ZMod ((moment P F).modulus q))

noncomputable def momentValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  (IntegralBerkowitzBlockBits.momentFamily (characteristic P F)).value (IntegralCriticalFlatMomentBits.packet P q)

theorem moment_replies (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : MomentEntryMatches P F answer) (q : List Bool) (hq : Domain P F q) :
    MomentRepliesAt P F answer q := by
  intro i j
  let z := pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have HD : Domain P F (IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient z) :=
    matrixWriter_domain P F .derivativeCoefficient z (by simpa only [z, pairFst_pair] using hq)
  have HS : selected P F .derivativeCoefficient (IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient z) = true :=
    (selected_iff P F .derivativeCoefficient _).mpr ⟨HD, IntegralCriticalFlatMatrixQuery.writer_phase P .derivativeCoefficient z⟩
  exact (hx _ HS).trans (moment_entry_child P F g q hq.1 i j)

noncomputable def stage2 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := encBits
  controller := IntegralBlockMomentBits.RecursiveStage.controller (moment P F) (momentAccess P a F h)
    (IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient)
  certificates := IntegralBlockMomentBits.RecursiveStage.certificates (moment P F) (momentAccess P a F h)
    (IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient) (IntegralCriticalFlatMatrixQuery.writer_FP P a .derivativeCoefficient)
  selected := selected P F .clearedHeight
  selected_FP := selected_FP P a F h .clearedHeight
  model := momentValue P F
  clock := IntegralCriticalFlatMomentBits.clock P (characteristic P F)
  clock_binary := IntegralCriticalFlatMomentBits.clock_binary P a (characteristic P F) (characteristicAccess P a F h)
  stateBound := IntegralCriticalFlatMomentBits.stateBound P (characteristic P F)
  stateBound_unary := IntegralCriticalFlatMomentBits.stateBound_unary P a (characteristic P F) (characteristicAccess P a F h)

attribute [local irreducible] IntegralMixedPscCharacteristicBits.source characteristicAccess

theorem correct2 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : MomentEntryMatches P F answer) :
    Correct (stage2 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q hq
    have H := (selected_iff P F .clearedHeight q).mp hq
    exact ModularRecursiveStage.halted_after_local (IntegralBlockMomentBits.powerAccess (moment P F) (momentAccess P a F h))
      (IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient) answer q (moment_replies P F g answer hx q H.1)
  · intro q t hq hh
    have H := (selected_iff P F .clearedHeight q).mp hq
    exact (ModularRecursiveStage.output_when_halted_local (IntegralBlockMomentBits.powerAccess (moment P F) (momentAccess P a F h))
      (IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient) answer q (moment_replies P F g answer hx q H.1) t hh).trans
      ((congrFun (IntegralBlockMomentBits.power_value (moment P F)) q).trans
        (IntegralBlockMomentBits.Family.requery_value _ _ q))
  · intro q t hq
    have H := (selected_iff P F .clearedHeight q).mp hq
    change (((IntegralBlockMomentBits.RecursiveStage.controller (moment P F) (momentAccess P a F h)
      (IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient)).reference answer)^[t]
      ((IntegralBlockMomentBits.RecursiveStage.controller (moment P F) (momentAccess P a F h)
        (IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient)).initial q)).length ≤ _
    exact ModularRecursiveStage.state_length_local
      (IntegralBlockMomentBits.powerAccess (moment P F) (momentAccess P a F h))
      (IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient) answer q (moment_replies P F g answer hx q H.1) t

  · intro q c budget hq hc
    have H := (selected_iff P F .clearedHeight q).mp hq
    obtain ⟨i, j, rfl⟩ := ModularRecursiveStage.requests_in_bounds_local
      (IntegralBlockMomentBits.powerAccess (moment P F) (momentAccess P a F h))
      (IntegralCriticalFlatMatrixQuery.writer P .derivativeCoefficient) answer q (moment_replies P F g answer hx q H.1) budget c hc
    have HP := H.2
    change phase q = 2 at HP
    have HF := IntegralMixedMatrixFrames.matrix_frame P .derivativeCoefficient
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
      (by simp only [pairFst_pair]; change 1 < phase q; omega)
    simpa only [pairFst_pair] using HF

end LeanCanny.Algebra.IntegralMixedPscUpperBits

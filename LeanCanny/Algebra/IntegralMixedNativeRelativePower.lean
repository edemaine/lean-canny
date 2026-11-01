/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNativeReductionPower
public import LeanCanny.Algebra.IntegralMixedVirtualRelativeModel
/-! # Native relative characteristic coefficients over virtual prefixes -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev FactorMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → isPhase .relativeFactor q →
    answer q = IntegralMixedVirtualMatrixBits.relativeFactor P F q

abbrev FactorRepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i j : Fin (IntegralBerkowitzBlockBits.powerDimension (characteristic P F) q),
    answer (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((characteristic P F).powerMatrix q i j : ℤ) : ZMod ((characteristic P F).modulus q))

theorem factor_replies (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : FactorMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1) : FactorRepliesAt P F answer q := by
  intro i j
  let c := IntegralCriticalFlatMatrixQuery.writer P .relativeFactor
    (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HC : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid
    simp only [c, IntegralCriticalFlatMatrixQuery.writer_birth, IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P c = 1 := by
    simpa only [c, IntegralMixedMatrixFrames.matrix_routine, pairFst_pair] using hr
  have HP : isPhase .relativeFactor c := IntegralCriticalFlatMatrixQuery.writer_phase P .relativeFactor _
  have HV := (hx c HC HR HP).trans (relativeFactor_child P F g q hv i j)
  exact HV

noncomputable def stage24 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := encBits
  controller := IntegralBerkowitzBlockBits.RecursiveStage.controller (characteristic P F) (characteristicAccess P a F h)
    (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor)
  certificates := IntegralBerkowitzBlockBits.RecursiveStage.certificates (characteristic P F) (characteristicAccess P a F h)
    (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor) (IntegralCriticalFlatMatrixQuery.writer_FP P a .relativeFactor)
  selected := selected P .relativePower
  selected_FP := selected_FP P a .relativePower
  model := (characteristic P F).value
  clock := ModularRecursiveStage.clock (IntegralBerkowitzBlockBits.powerFamily (characteristic P F))
  clock_binary := IntegralBerkowitzBlockBits.RecursiveStage.clock_binary (characteristic P F) (characteristicAccess P a F h)
  stateBound := ModularRecursiveStage.stateBound (IntegralBerkowitzBlockBits.powerFamily (characteristic P F))
  stateBound_unary := IntegralBerkowitzBlockBits.RecursiveStage.stateBound_unary (characteristic P F) (characteristicAccess P a F h)

attribute [local irreducible] characteristic characteristicAccess

theorem correct24 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool) (hx : FactorMatches P F answer) :
    Correct (stage24 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q hq
    have H := (selected_iff P .relativePower q).mp hq
    exact IntegralBerkowitzBlockBits.RecursiveStage.halted_after_local (characteristic P F) (characteristicAccess P a F h)
      (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor) answer q (factor_replies P F g answer hx q H.1 H.2.1)
  · intro q t hq hh
    have H := (selected_iff P .relativePower q).mp hq
    exact IntegralBerkowitzBlockBits.RecursiveStage.output_when_halted_local (characteristic P F) (characteristicAccess P a F h)
      (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor) answer q (factor_replies P F g answer hx q H.1 H.2.1) t hh
  · intro q t hq
    have H := (selected_iff P .relativePower q).mp hq
    simpa only [stage24, encBits_apply] using IntegralBerkowitzBlockBits.RecursiveStage.state_length_local
      (characteristic P F) (characteristicAccess P a F h) (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor)
      answer q (factor_replies P F g answer hx q H.1 H.2.1) t
  · intro q c budget hq hc
    have H := (selected_iff P .relativePower q).mp hq
    obtain ⟨i, j, rfl⟩ := IntegralBerkowitzBlockBits.RecursiveStage.requests_in_bounds_local
      (characteristic P F) (characteristicAccess P a F h) (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor)
      answer q (factor_replies P F g answer hx q H.1 H.2.1) budget c hc
    have HP := H.2.2
    have HS : Phase.relativeFactor.code < phase (pairFst
        (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) := by
      simp only [pairFst_pair]
      change 23 < phase q
      change phase q = 24 at HP
      omega
    simpa only [pairFst_pair] using IntegralMixedMatrixFrames.matrix_frame P .relativeFactor
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) HS

end LeanCanny.Algebra.IntegralMixedVirtualUpperBits

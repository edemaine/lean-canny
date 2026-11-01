/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationRelativeModel
public import LeanCanny.Computation.NativeSingleCallBranch
/-! # Native characteristic coefficients for the actual normalization matrix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def selected (P : Parameters) (p : Phase) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 5 ∧ isPhase p q)

theorem selected_FP (P : Parameters) (a : Access P) (p : Phase) : (fun q => [selected P p q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 5)).and (isPhase_FP p))).flag_mem_FP

theorem selected_iff (P : Parameters) (p : Phase) (q : List Bool) : selected P p q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 5 ∧ isPhase p q := by
  simp only [selected, decide_eq_true_eq]

abbrev FactorMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 → isPhase .productEntry q →
    answer q = factorValue P F q

abbrev FactorRepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i j : Fin (IntegralBerkowitzBlockBits.powerDimension (source P F) q),
    answer (IntegralCriticalFlatMatrixQuery.writer P .productEntry
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((source P F).powerMatrix q i j : ℤ) : ZMod ((source P F).modulus q))

theorem factor_replies (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : FactorMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 5) : FactorRepliesAt P F answer q := by
  intro i j
  let c := IntegralCriticalFlatMatrixQuery.writer P .productEntry
    (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HC : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid
    simp only [c, IntegralCriticalFlatMatrixQuery.writer_birth, IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P c = 5 := by
    simpa only [c, IntegralMixedMatrixFrames.matrix_routine, pairFst_pair] using hr
  have HP : isPhase .productEntry c := IntegralCriticalFlatMatrixQuery.writer_phase P .productEntry _
  exact (hx c HC HR HP).trans (factor_child P F g .productEntry q hv i j)

noncomputable def stage6 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := encBits
  controller := IntegralBerkowitzBlockBits.RecursiveStage.controller (source P F) (access P a F h)
    (IntegralCriticalFlatMatrixQuery.writer P .productEntry)
  certificates := IntegralBerkowitzBlockBits.RecursiveStage.certificates (source P F) (access P a F h)
    (IntegralCriticalFlatMatrixQuery.writer P .productEntry) (IntegralCriticalFlatMatrixQuery.writer_FP P a .productEntry)
  selected := selected P .productPower
  selected_FP := selected_FP P a .productPower
  model := (source P F).value
  clock := ModularRecursiveStage.clock (IntegralBerkowitzBlockBits.powerFamily (source P F))
  clock_binary := IntegralBerkowitzBlockBits.RecursiveStage.clock_binary (source P F) (access P a F h)
  stateBound := ModularRecursiveStage.stateBound (IntegralBerkowitzBlockBits.powerFamily (source P F))
  stateBound_unary := IntegralBerkowitzBlockBits.RecursiveStage.stateBound_unary (source P F) (access P a F h)

attribute [local irreducible] source access

theorem correct6 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool) (hx : FactorMatches P F answer) :
    Correct (stage6 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q hq
    have H := (selected_iff P .productPower q).mp hq
    exact IntegralBerkowitzBlockBits.RecursiveStage.halted_after_local (source P F) (access P a F h)
      (IntegralCriticalFlatMatrixQuery.writer P .productEntry) answer q (factor_replies P F g answer hx q H.1 H.2.1)
  · intro q t hq hh
    have H := (selected_iff P .productPower q).mp hq
    exact IntegralBerkowitzBlockBits.RecursiveStage.output_when_halted_local (source P F) (access P a F h)
      (IntegralCriticalFlatMatrixQuery.writer P .productEntry) answer q (factor_replies P F g answer hx q H.1 H.2.1) t hh
  · intro q t hq
    have H := (selected_iff P .productPower q).mp hq
    simpa only [stage6, encBits_apply] using IntegralBerkowitzBlockBits.RecursiveStage.state_length_local
      (source P F) (access P a F h) (IntegralCriticalFlatMatrixQuery.writer P .productEntry) answer q
      (factor_replies P F g answer hx q H.1 H.2.1) t
  · intro q c budget hq hc
    have H := (selected_iff P .productPower q).mp hq
    obtain ⟨i, j, rfl⟩ := IntegralBerkowitzBlockBits.RecursiveStage.requests_in_bounds_local
      (source P F) (access P a F h) (IntegralCriticalFlatMatrixQuery.writer P .productEntry) answer q
      (factor_replies P F g answer hx q H.1 H.2.1) budget c hc
    have HP := H.2.2
    change phase q = 6 at HP
    have HF := IntegralMixedMatrixFrames.matrix_frame P .productEntry
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
      (by simp only [pairFst_pair]; change 5 < phase q; omega)
    simpa only [pairFst_pair] using HF

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits

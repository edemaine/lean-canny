/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextReductionPower
public import LeanCanny.Algebra.IntegralMixedVirtualRelativeModel
/-! # Native relative characteristic coefficients over virtual prefixes -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open IntegralMixedVirtualUpperBits
set_option backward.isDefEq.respectTransparency false

abbrev FactorRepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i j : Fin (IntegralBerkowitzBlockBits.powerDimension (characteristic P F) q),
    answer (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((characteristic P F).powerMatrix q i j : ℤ) : ZMod ((characteristic P F).modulus q))

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
    (answer : List Bool → List Bool)
    (hx : ∀ q, selected P .relativePower q = true → FactorRepliesAt P F answer q) :
    Correct (stage24 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q hq
    have H := selected_base P .relativePower q hq
    exact IntegralBerkowitzBlockBits.RecursiveStage.halted_after_local (characteristic P F) (characteristicAccess P a F h)
      (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor) answer q (hx q hq)
  · intro q t hq hh
    have H := selected_base P .relativePower q hq
    exact IntegralBerkowitzBlockBits.RecursiveStage.output_when_halted_local (characteristic P F) (characteristicAccess P a F h)
      (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor) answer q (hx q hq) t hh
  · intro q t hq
    have H := selected_base P .relativePower q hq
    simpa only [stage24, encBits_apply] using IntegralBerkowitzBlockBits.RecursiveStage.state_length_local
      (characteristic P F) (characteristicAccess P a F h) (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor)
      answer q (hx q hq) t
  · intro q c budget hq hc
    have H := selected_base P .relativePower q hq
    obtain ⟨i, j, rfl⟩ := IntegralBerkowitzBlockBits.RecursiveStage.requests_in_bounds_local
      (characteristic P F) (characteristicAccess P a F h) (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor)
      answer q (hx q hq) budget c hc
    have HP := H.2.2
    have HS : Phase.relativeFactor.code < phase (pairFst
        (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) := by
      simp only [pairFst_pair]
      change 23 < phase q
      change phase q = 24 at HP
      omega
    simpa only [pairFst_pair] using IntegralMixedMatrixFrames.matrix_frame P .relativeFactor
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) HS

end LeanCanny.Algebra.IntegralMixedVirtualContextUpperBits

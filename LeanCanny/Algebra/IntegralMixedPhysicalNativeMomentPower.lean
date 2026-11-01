/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeReductionPower
public import LeanCanny.Algebra.IntegralMixedPhysicalMomentSnapshot
/-! # Native physical moment powering from current augmented entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable def stage22 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := encBits
  controller := IntegralCriticalFlatMomentBits.controller P a (characteristic P F) (characteristicAccess P a F h)
  certificates := IntegralCriticalFlatMomentBits.certificates P a (characteristic P F) (characteristicAccess P a F h)
  selected := selected P .momentPower
  selected_FP := selected_FP P a .momentPower
  model := momentValue P F
  clock := IntegralCriticalFlatMomentBits.clock P (characteristic P F)
  clock_binary := IntegralCriticalFlatMomentBits.clock_binary P a (characteristic P F) (characteristicAccess P a F h)
  stateBound := IntegralCriticalFlatMomentBits.stateBound P (characteristic P F)
  stateBound_unary := IntegralCriticalFlatMomentBits.stateBound_unary P a (characteristic P F) (characteristicAccess P a F h)

attribute [local irreducible] characteristic characteristicAccess

theorem correct22 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (answer : List Bool → List Bool)
    (he : ∀ q, selected P .momentPower q = true → IntegralCriticalFlatMomentBits.RepliesAt P (characteristic P F) answer q) :
    Correct (stage22 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q hq
    exact IntegralCriticalFlatMomentBits.halted_after P a (characteristic P F) (characteristicAccess P a F h) answer q (he q hq)
  · intro q t hq hh
    exact IntegralCriticalFlatMomentBits.output_when_halted P a (characteristic P F) (characteristicAccess P a F h) answer q (he q hq) t hh
  · intro q t hq
    simpa only [stage22, encBits_apply] using IntegralCriticalFlatMomentBits.state_length P a (characteristic P F)
      (characteristicAccess P a F h) answer q (he q hq) t
  · intro q c budget hq hc
    obtain ⟨i, j, rfl⟩ := ModularRecursiveStage.requests_in_bounds_local
      (IntegralBlockMomentBits.powerAccess (IntegralCriticalFlatMomentBits.source P (characteristic P F))
        (IntegralCriticalFlatMomentBits.access P a (characteristic P F) (characteristicAccess P a F h)))
      (IntegralCriticalFlatMatrixQuery.writer P .momentEntry) answer q (he q hq) budget c hc
    have HP := (selected_base P .momentPower q hq).2.2
    have HS : Phase.momentEntry.code < phase (pairFst
        (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) := by
      simp only [pairFst_pair]
      change 21 < phase q
      change phase q = 22 at HP
      omega
    simpa only [pairFst_pair] using IntegralMixedMatrixFrames.matrix_frame P .momentEntry
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) HS

end LeanCanny.Algebra.IntegralMixedPhysicalUpperBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalComponent
/-! # Physical upper requests inherit actual context-limited component replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalUpperReplyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalUpperBits IntegralMixedPhysicalComponentBits
set_option backward.isDefEq.respectTransparency false

abbrev LeadingCallback (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedPhysicalContextBits.selected P .criticalCoefficient q = true ∨
    IntegralMixedPhysicalContextBits.selected P .reductionEntry q = true →
    answer (IntegralMixedScalarQueryBits.commonLeading P q) = commonLeading P F (IntegralMixedScalarQueryBits.commonLeading P q)

theorem current (P : Parameters) (F : Family) (answer : List Bool → List Bool) (hm : Matches P F answer)
    (p : Phase) (hp : p.code ≤ 25) (q c : List Bool)
    (hroot : RankedHistoryTask.root c = RankedHistoryTask.root q) (hbirth : birth P c = birth P q)
    (hroutine : IntegralMixedRoutineTaskBits.routine P c = IntegralMixedRoutineTaskBits.routine P q)
    (hcontext : get P .slot15 c = get P .slot15 q)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1)
    (hx : get P .slot15 q = 1) (hc : isPhase p c) : answer c = component P F p c :=
  hm p c hp (IntegralMixedPhysicalContextReplyBits.current_selected P p q c hroot hbirth hroutine hcontext hv hr hx hc)

theorem matrix (P : Parameters) (F : Family) (answer : List Bool → List Bool) (hm : Matches P F answer)
    (p : Phase) (hp : p.code ≤ 25) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1)
    (hx : get P .slot15 (pairFst z) = 1) :
    answer (IntegralCriticalFlatMatrixQuery.writer P p z) = component P F p (IntegralCriticalFlatMatrixQuery.writer P p z) :=
  hm p _ hp (IntegralMixedPhysicalContextReplyBits.matrix_selected P p z hv hr hx)

theorem next (P : Parameters) (F : Family) (answer : List Bool → List Bool) (hm : Matches P F answer)
    (p : Phase) (hp : p.code ≤ 25) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1) (hx : get P .slot15 q = 1) :
    answer (IntegralCriticalFlatEulerBits.next P p q) = component P F p (IntegralCriticalFlatEulerBits.next P p q) := by
  apply current P F answer hm p hp _ _ (IntegralCriticalFlatEulerBits.next_root P p q)
    (IntegralCriticalFlatEulerBits.next_birth P p q) _ (IntegralCriticalFlatEulerBits.next_get P p q .slot15) hv hr hx
    (IntegralCriticalFlatEulerBits.next_phase P p q)
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatEulerBits.next_get]

theorem reduction_current (P : Parameters) (F : Family) (answer : List Bool → List Bool) (hm : Matches P F answer)
    (q : List Bool) (hq : selected P .reductionPower q = true) : ReductionRepliesAt P F answer q := by
  intro i j
  have H := selected_base P .reductionPower q hq
  have HX := ((IntegralMixedPhysicalContextBits.selected_iff P .reductionPower q).mp hq).2
  exact matrix P F answer hm .reductionEntry (by decide) _
    (by simpa only [pairFst_pair] using H.1) (by simpa only [pairFst_pair] using H.2.1) (by simpa only [pairFst_pair] using HX)

theorem power_current (P : Parameters) (F : Family) (answer : List Bool → List Bool) (hm : Matches P F answer)
    (q : List Bool) (hq : selected P .actionEntry q = true) : ActionRepliesAt P F answer q := by
  intro _
  have H := selected_base P .actionEntry q hq
  have HX := ((IntegralMixedPhysicalContextBits.selected_iff P .actionEntry q).mp hq).2
  exact next P F answer hm .reductionPower (by decide) q H.1 H.2.1 HX

theorem factor_current (P : Parameters) (F : Family) (g : IntegralMixedPhysicalCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hm : Matches P F answer)
    (q : List Bool) (hq : selected P .relativePower q = true) : FactorRepliesAt P F answer q := by
  intro i j
  have H := selected_base P .relativePower q hq
  have HX := ((IntegralMixedPhysicalContextBits.selected_iff P .relativePower q).mp hq).2
  have HM := matrix P F answer hm .relativeFactor (by decide)
    (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
    (by simpa only [pairFst_pair] using H.1) (by simpa only [pairFst_pair] using H.2.1) (by simpa only [pairFst_pair] using HX)
  exact HM.trans (relativeFactor_child P F g q i j)

theorem coefficient_current (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hm : Matches P F answer) (hl : LeadingCallback P F answer)
    (q : List Bool) (hq : selected P .criticalCoefficient q = true) : CoefficientRepliesAt P F answer q := by
  have H := selected_base P .criticalCoefficient q hq
  have HX := ((IntegralMixedPhysicalContextBits.selected_iff P .criticalCoefficient q).mp hq).2
  exact ⟨(next P F answer hm .relativePower (by decide) q H.1 H.2.1 HX).trans
    (characteristic_next P F .relativePower q), (hl q (Or.inl hq)).trans (commonLeading_child P F q)⟩
end LeanCanny.Algebra.IntegralMixedPhysicalUpperReplyBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeUpperSingles
/-! # Actual streamed upper branches use only their current finite replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relative relativeAccess reduction reductionAccess characteristic characteristicAccess
  IntegralCriticalTotalCreatingBits.atFamily

theorem correct18 (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x) :
    Correct (stage18 F h) (answer F x) (Frame F) := by
  constructor
  · intro q hq
    exact IntegralCriticalFlatReductionPowerBits.halted_after_local F.toParameters h.task.toAccess (reduction F)
      (reductionAccess F h) (reductionControls F h) _ q (replies18 F x hx q ((selected_iff F .reductionPower q).mp hq).1)
  · intro q t hq hh
    exact IntegralCriticalFlatReductionPowerBits.output_when_halted_local F.toParameters h.task.toAccess (reduction F)
      (reductionAccess F h) (reductionControls F h) _ q (replies18 F x hx q ((selected_iff F .reductionPower q).mp hq).1) t hh
  · intro q t hq
    simpa only [stage18, encBits_apply] using IntegralCriticalFlatReductionPowerBits.state_length_local F.toParameters h.task.toAccess (reduction F)
      (reductionAccess F h) (reductionControls F h) _ q (replies18 F x hx q ((selected_iff F .reductionPower q).mp hq).1) t
  · intro q c budget hq hc
    have H := (selected_iff F .reductionPower q).mp hq
    exact IntegralCriticalFlatReductionPowerBits.requests_frame_local F.toParameters h.task.toAccess (reduction F)
      (reductionAccess F h) (reductionControls F h) _ q (replies18 F x hx q H.1) budget c H.2 hc

theorem correct22 (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x) :
    Correct (stage22 F h) (answer F x) (Frame F) := by
  constructor
  · intro q hq
    exact IntegralCriticalFlatMomentBits.halted_after F.toParameters h.task.toAccess (characteristic F) (characteristicAccess F h)
      _ q (replies22 F x hx q ((selected_iff F .momentPower q).mp hq).1)
  · intro q t hq hh
    exact IntegralCriticalFlatMomentBits.output_when_halted F.toParameters h.task.toAccess (characteristic F) (characteristicAccess F h)
      _ q (replies22 F x hx q ((selected_iff F .momentPower q).mp hq).1) t hh
  · intro q t hq
    simpa only [stage22, encBits_apply] using IntegralCriticalFlatMomentBits.state_length F.toParameters h.task.toAccess (characteristic F)
      (characteristicAccess F h) _ q (replies22 F x hx q ((selected_iff F .momentPower q).mp hq).1) t
  · intro q c budget hq hc
    have H := (selected_iff F .momentPower q).mp hq
    exact IntegralCriticalFlatMomentBits.requests_frame F.toParameters h.task.toAccess (characteristic F) (characteristicAccess F h)
      _ q (replies22 F x hx q H.1) budget c H.2 hc

theorem correct24 (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x) :
    Correct (stage24 F h) (answer F x) (Frame F) := by
  constructor
  · intro q hq
    exact IntegralCriticalFlatActualRelativeBits.halted_after F h _ q (replies24 F x hx q ((selected_iff F .relativePower q).mp hq).1)
  · intro q t hq hh
    exact IntegralCriticalFlatActualRelativeBits.output_when_halted F h _ q (replies24 F x hx q ((selected_iff F .relativePower q).mp hq).1) t hh
  · intro q t hq
    simpa only [stage24, encBits_apply] using IntegralCriticalFlatActualRelativeBits.state_length F h _ q
      (replies24 F x hx q ((selected_iff F .relativePower q).mp hq).1) t
  · intro q c budget hq hc
    have H := (selected_iff F .relativePower q).mp hq
    exact IntegralCriticalFlatActualRelativeBits.requests_frame F h _ q (replies24 F x hx q H.1) budget c H.2 hc

end LeanCanny.Algebra.IntegralCriticalNativeUpperBits

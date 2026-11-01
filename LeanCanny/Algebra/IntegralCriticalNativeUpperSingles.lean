/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeUpperSingleValues
/-! # Native local contracts for all upper single-call stages -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relative relativeAccess reduction reductionAccess characteristic characteristicAccess
  IntegralCriticalTotalCreatingBits.atFamily

theorem correct17 (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x) :
    Correct (stage17 F h) (answer F x) (Frame F) := by
  unfold stage17
  apply single_correct
  · intro q hq
    have H := (selectedFinite_iff F .reductionEntry _ q).mp hq
    exact value17 F h x hx q H.1 H.2.2
  · intro q c budget hq hc
    exact frame17 F h _ budget q c ((selectedFinite_iff F .reductionEntry _ q).mp hq).2.1 hc

theorem correct19 (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x) :
    Correct (stage19 F h) (answer F x) (Frame F) := by
  unfold stage19
  apply single_correct
  · intro q hq
    have H := (selectedFinite_iff F .actionEntry _ q).mp hq
    exact value19 F x hx q H.1 H.2.2
  · intro q c budget hq hc
    exact frame19 F _ budget q c ((selectedFinite_iff F .actionEntry _ q).mp hq).2.1 hc

theorem correct21 (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x) :
    Correct (stage21 F h) (answer F x) (Frame F) := by
  unfold stage21
  apply single_correct
  · intro q hq
    have H := (selected_iff F .momentEntry q).mp hq
    exact value21 F h x hx q H.1 H.2
  · intro q c budget hq hc
    exact frame21 F h _ budget q c ((selected_iff F .momentEntry q).mp hq).2 hc

theorem correct23 (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x) :
    Correct (stage23 F h) (answer F x) (Frame F) := by
  unfold stage23
  apply single_correct
  · intro q hq
    have H := (selectedFinite_iff F .relativeFactor _ q).mp hq
    exact value23 F h x hx q H.1 H.2.2
  · intro q c budget hq hc
    exact frame23 F _ budget q c ((selectedFinite_iff F .relativeFactor _ q).mp hq).2.1 hc

theorem correct25 (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x) :
    Correct (stage25 F h) (answer F x) (Frame F) := by
  unfold stage25
  apply single_correct
  · intro q hq
    exact value25 F x hx q ((selected_iff F .criticalCoefficient q).mp hq).1
  · intro q c budget hq hc
    exact frame25 F _ budget q c ((selected_iff F .criticalCoefficient q).mp hq).2 hc

theorem correct26 (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hx : Matches F x) :
    Correct (stage26 F h) (answer F x) (Frame F) := by
  unfold stage26
  apply single_correct
  · intro q _
    exact value26 F x hx q
  · intro q c budget hq hc
    exact frame26 F _ budget q c ((selected_iff F .companion q).mp hq).2 hc

end LeanCanny.Algebra.IntegralCriticalNativeUpperBits

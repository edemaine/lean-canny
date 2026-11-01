/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.NativeOracleAgreement
/-! # Request invariants compose across native branch choices -/
@[expose] public section
namespace LeanCanny.Computation.NativeControllerBranch
open RecursiveController
set_option backward.isDefEq.respectTransparency false

def RequestsSatisfy (M : Machine) (answer : List Bool → List Bool) (R : List Bool → List Bool → Prop) : Prop :=
  ∀ q, M.selected q = true → ∀ budget c, M.controller.Requests answer budget q c → R q c

theorem requestsSatisfy_choose (M N : Machine) (answer : List Bool → List Bool) (R : List Bool → List Bool → Prop)
    (hM : RequestsSatisfy M answer R) (hN : RequestsSatisfy N answer R) : RequestsSatisfy (M.choose N) answer R := by
  let : Inhabited M.State := ⟨M.defaultValue⟩
  let : Inhabited N.State := ⟨N.defaultValue⟩
  intro q hq budget c hc
  change (Controller.choose M.selected M.controller N.controller).Requests answer budget q c at hc
  rw [Controller.choose_requests_iff] at hc
  cases hs : M.selected q with
  | true => exact hM q hs budget c (by simpa only [hs, ite_true] using hc)
  | false =>
    have HN : N.selected q = true := by change (_ || _) = true at hq; simpa only [hs, Bool.false_or] using hq
    exact hN q HN budget c (by simpa only [hs, Bool.false_eq_true, ite_false] using hc)

theorem requestsSatisfy_withGuard (M : Machine) (selected : List Bool → Bool) (hs : (fun q => [selected q]) ∈ FP)
    (answer : List Bool → List Bool) (R : List Bool → List Bool → Prop) (hM : RequestsSatisfy M answer R)
    (hi : ∀ q, selected q = true → M.selected q = true) : RequestsSatisfy (M.withGuard selected hs) answer R :=
  fun q hq budget c hc => hM q (hi q hq) budget c hc

theorem requestsSatisfy_zero (answer : List Bool → List Bool) (R : List Bool → List Bool → Prop) : RequestsSatisfy zero answer R := by
  intro q _ budget c hc
  obtain ⟨hr, _⟩ := (zeroProgram.requests_iff answer budget q c).mp hc
  cases hr
end LeanCanny.Computation.NativeControllerBranch

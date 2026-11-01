/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.ControllerOracleAgreement
public import LeanCanny.Computation.NativeSingleCallBranch
/-! # Restricting native branches needs agreement only on their observed requests -/
@[expose] public section
namespace LeanCanny.Computation.NativeControllerBranch
open RecursiveController
set_option backward.isDefEq.respectTransparency false

theorem withGuard_oracle_correct (M : Machine) (select : List Bool → Bool)
    (hs : (fun q => [select q]) ∈ FP) (a b : List Bool → List Bool)
    (frame : List Bool → List Bool → Prop) (ha : Correct M a frame)
    (hsub : ∀ q, select q = true → M.selected q = true)
    (hab : ∀ q, select q = true → ∀ budget child,
      M.controller.Requests a budget q child → a child = b child) :
    Correct (M.withGuard select hs) b frame := by
  have he (q : List Bool) (hq : select q = true) (t : ℕ) :
      (M.controller.reference a)^[t] (M.controller.initial q) =
        (M.controller.reference b)^[t] (M.controller.initial q) :=
    M.controller.iterate_eq_of_requests a b q t (fun child hc => hab q hq (fun _ => t) child hc)
  constructor
  · intro q hq
    change M.controller.halted ((M.controller.reference b)^[M.clock q] (M.controller.initial q)) = true
    rw [← he q hq (M.clock q)]
    exact ha.halted q (hsub q hq)
  · intro q t hq hh
    change M.controller.halted ((M.controller.reference b)^[t] (M.controller.initial q)) = true at hh
    change M.controller.output ((M.controller.reference b)^[t] (M.controller.initial q)) = M.model q
    rw [← he q hq t] at hh ⊢
    exact ha.output q t (hsub q hq) hh
  · intro q t hq
    change (M.encoding ((M.controller.reference b)^[t] (M.controller.initial q))).length ≤ M.stateBound q
    rw [← he q hq t]
    exact ha.state q t (hsub q hq)
  · intro q child budget hq hc
    change M.controller.Requests b budget q child at hc
    exact ha.requests q child budget (hsub q hq)
      ((M.controller.requests_iff_of_iterates a b q child budget (he q hq)).mpr hc)

end LeanCanny.Computation.NativeControllerBranch

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.ControllerRequests
/-! # Controller orbits depend only on answers to actual requests -/
@[expose] public section
namespace LeanCanny.Computation.RecursiveController.Controller
variable {Q S : Type} (C : Controller Q S)

theorem iterate_eq_of_requests (a b : Q → List Bool) (q : Q) (t : ℕ)
    (hab : ∀ child, C.Requests a (fun _ => t) q child → a child = b child) :
    (C.reference a)^[t] (C.initial q) = (C.reference b)^[t] (C.initial q) := by
  have all : ∀ u, u ≤ t → (C.reference a)^[u] (C.initial q) = (C.reference b)^[u] (C.initial q) := by
    intro u
    induction u with
    | zero => intro _; rfl
    | succ u ih =>
      intro hu
      have he := ih (by omega)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← he]
      let s := (C.reference a)^[u] (C.initial q)
      change C.reference a s = C.reference b s
      by_cases hh : C.halted s = true
      · simp only [reference, hh, ite_true]
      · by_cases hn : C.needs s = true
        · have ha := hab (C.query s)
            ⟨u, (show u ≤ t from by omega), Bool.eq_false_of_not_eq_true hh, hn, rfl⟩
          simp only [reference, hh, hn, ite_true]
          rw [ha]
        · simp only [reference, hh, hn, Bool.false_eq_true, ite_false]
  exact all t (Nat.le_refl _)

theorem requests_iff_of_iterates (a b : Q → List Bool) (q child : Q) (budget : Q → ℕ)
    (he : ∀ t, (C.reference a)^[t] (C.initial q) = (C.reference b)^[t] (C.initial q)) :
    C.Requests a budget q child ↔ C.Requests b budget q child := by
  unfold Requests
  simp_rw [he]

end LeanCanny.Computation.RecursiveController.Controller

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.ControllerDispatch
public import LeanCanny.Computation.SingleCallController

/-! # Requests along bounded controller orbits

Requests retain the halted guard: a controller may still report that it needs
an answer after it has halted. Preparing an input changes only the initial
state, so requests keep their original child task identifiers.
-/

@[expose] public section

namespace LeanCanny.Computation.RecursiveController.Controller
open Turing.MultiTapeTM

variable {Q S : Type} (C : Controller Q S)

def Requests (answer : Q → List Bool) (budget : Q → ℕ) (q child : Q) : Prop :=
  ∃ t, t ≤ budget q ∧
    C.halted ((C.reference answer)^[t] (C.initial q)) = false ∧
    C.needs ((C.reference answer)^[t] (C.initial q)) = true ∧
    child = C.query ((C.reference answer)^[t] (C.initial q))

theorem requests_of_valid {answer : Q → List Bool} {tasks : Q → Prop} {budget : Q → ℕ}
    {f : Frame Q S} (hf : C.Valid answer tasks budget f)
    (hh : C.halted f.2 = false) (hn : C.needs f.2 = true) :
    C.Requests answer budget f.1 (C.query f.2) := by
  obtain ⟨_, t, ht, he⟩ := hf
  exact ⟨t, ht, he ▸ hh, he ▸ hn, congrArg C.query he⟩

theorem choose_requests_iff {A B : Type} [Inhabited A] [Inhabited B]
    (select : Q → Bool) (C : Controller Q A) (D : Controller Q B)
    (answer : Q → List Bool) (budget : Q → ℕ) (q child : Q) :
    (choose select C D).Requests answer budget q child ↔
      if select q then C.Requests answer budget q child else D.Requests answer budget q child := by
  cases hs : select q <;>
    simp only [Requests, choose_halted_iterate, choose_needs_iterate, choose_query_iterate,
      hs, Bool.false_eq_true, ite_false, ite_true]

theorem prepare_requests_iff (input : Q → Q) (answer : Q → List Bool)
    (budget : Q → ℕ) (q child : Q) :
    (prepare C input).Requests answer budget q child ↔
      C.Requests answer (fun _ => budget q) (input q) child := Iff.rfl

/-- Orbit contracts avoid exposing the representation of valid frames to
clients. Task closure remains relative to the original root. -/
theorem evaluatorOfOrbits {encQ : Q ↪ List Bool} {encS : S ↪ List Bool}
    [Inhabited Q] [Inhabited S]
    (hC : C.Certificates (encQ := encQ) (encS := encS))
    (answer : Q → List Bool) (rank budget : Q → ℕ) (tasks : Q → Q → Prop) (N R B : Q → ℕ)
    (hN : ComputableTidilyInPolyTime N encQ encNat)
    (hR : ComputableTidilyInPolyTime R encQ encUnary)
    (hB : PolyBounded (fun q => (encQ q).length) B)
    (hroot : ∀ q, tasks q q)
    (hstop : ∀ root q, tasks root q → C.halted ((C.reference answer)^[budget q] (C.initial q)) = true)
    (hb : ∀ root q, tasks root q → budget q ≤ N root)
    (hdone : ∀ root q t, tasks root q → t ≤ budget q →
      C.halted ((C.reference answer)^[t] (C.initial q)) = true →
      C.output ((C.reference answer)^[t] (C.initial q)) = answer q)
    (hquery : ∀ root q t, tasks root q → t ≤ budget q →
      C.halted ((C.reference answer)^[t] (C.initial q)) = false →
      C.needs ((C.reference answer)^[t] (C.initial q)) = true →
      tasks root (C.query ((C.reference answer)^[t] (C.initial q))) ∧
        rank (C.query ((C.reference answer)^[t] (C.initial q))) < rank q)
    (hrank : ∀ root q, tasks root q → rank q ≤ R root)
    (htask : ∀ root q, tasks root q → (encQ q).length ≤ B root)
    (hstate : ∀ root q, tasks root q → ∀ t ≤ budget q,
      (encS ((C.reference answer)^[t] (C.initial q))).length ≤ B root)
    (hanswer : ∀ root q, tasks root q → (answer q).length ≤ B root) :
    ComputableTidilyInPolySpace answer encQ encBits := by
  apply C.evaluator hC answer rank budget tasks N R B hN hR hB hroot hstop hb
    ?_ ?_ hrank htask hstate hanswer
  · intro root f hf hh
    obtain ⟨hq, t, ht, he⟩ := hf
    rw [he] at hh ⊢
    exact hdone root f.1 t hq ht hh
  · intro root f hf hh hn
    obtain ⟨hq, t, ht, he⟩ := hf
    rw [he] at hh hn ⊢
    exact hquery root f.1 t hq ht hh hn

end LeanCanny.Computation.RecursiveController.Controller

namespace LeanCanny.Computation.SingleCall.Program

theorem requests_iff (P : Program) (answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (q child : List Bool) :
    P.controller.Requests answer budget q child ↔ P.request q = true ∧ child = P.query q := by
  constructor
  · rintro ⟨t, _, _, hn, he⟩
    change P.request (((P.controller.reference answer)^[t] (initial q)).1) = true at hn
    change child = P.query (((P.controller.reference answer)^[t] (initial q)).1) at he
    rw [P.context_iterate] at hn he
    exact ⟨hn, he⟩
  · rintro ⟨hr, he⟩
    refine ⟨0, Nat.zero_le _, ?_, ?_, ?_⟩
    · change Bool.not (P.request q) = false
      rw [hr]
      rfl
    · exact hr
    · exact he

end LeanCanny.Computation.SingleCall.Program

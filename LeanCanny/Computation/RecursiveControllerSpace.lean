/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.RecursiveController

/-! # Native polynomial space for recursively queried streamed controllers -/

@[expose] public section

namespace LeanCanny.Computation.RecursiveController.Controller
open RecursiveStack Turing.MultiTapeTM

variable {Q S : Type} {encQ : Q ↪ List Bool} {encS : S ↪ List Bool} (C : Controller Q S)

structure Certificates : Prop where
  initial : ComputableTidilyInPolySpace C.initial encQ encS
  halted : ComputableTidilyInPolySpace C.halted encS encBool
  output : ComputableTidilyInPolySpace C.output encS encBits
  needs : ComputableTidilyInPolySpace C.needs encS encBool
  query : ComputableTidilyInPolySpace C.query encS encQ
  advance : ComputableTidilyInPolySpace C.advance encS encS
  resume : ComputableTidilyInPolySpace C.resume (encPair encS encBits) encS

theorem instruction_computable (hC : C.Certificates (encQ := encQ) (encS := encS)) :
    ComputableTidilyInPolySpace C.instruction (encPair encQ encS) (encAction (encPair encQ encS)) := by
  rcases hC with ⟨hi, hh, ho, hn, hq, ha, hr⟩
  unfold instruction Action.done Action.call Action.next
  fun_prop (config := { maxSteps := 256 })

theorem receive_computable (hC : C.Certificates (encQ := encQ) (encS := encS)) :
    ComputableTidilyInPolySpace C.receive (encPair (encPair encQ encS) encBits) (encPair encQ encS) := by
  have hr := hC.resume
  unfold receive
  fun_prop

/-- Uniform recursive evaluation of a family of streamed algorithms. The
budget bounds logical oracle transitions; it is proof data and need not be FP.
All runtime operations are provided separately by `Certificates`. -/
theorem evaluator [Inhabited Q] [Inhabited S]
    (hC : C.Certificates (encQ := encQ) (encS := encS))
    (answer : Q → List Bool) (rank budget : Q → ℕ) (tasks : Q → Q → Prop) (N R B : Q → ℕ)
    (hN : ComputableTidilyInPolyTime N encQ encNat)
    (hR : ComputableTidilyInPolyTime R encQ encUnary)
    (hB : PolyBounded (fun q => (encQ q).length) B)
    (hroot : ∀ q, tasks q q)
    (hstop : ∀ root q, tasks root q → C.halted ((C.reference answer)^[budget q] (C.initial q)) = true)
    (hb : ∀ root q, tasks root q → budget q ≤ N root)
    (hdone : ∀ root f, C.Valid answer (tasks root) budget f → C.halted f.2 = true → C.output f.2 = answer f.1)
    (hquery : ∀ root f, C.Valid answer (tasks root) budget f → C.halted f.2 = false → C.needs f.2 = true →
      tasks root (C.query f.2) ∧ rank (C.query f.2) < rank f.1)
    (hrank : ∀ root q, tasks root q → rank q ≤ R root)
    (htask : ∀ root q, tasks root q → (encQ q).length ≤ B root)
    (hstate : ∀ root q, tasks root q → ∀ t ≤ budget q,
      (encS ((C.reference answer)^[t] (C.initial q))).length ≤ B root)
    (hanswer : ∀ root q, tasks root q → (answer q).length ≤ B root) :
    ComputableTidilyInPolySpace answer encQ encBits := by
  have hi : ComputableTidilyInPolySpace (fun q => (q, C.initial q)) encQ (encPair encQ encS) :=
    ComputableTidilyInPolySpace.id'.prod hC.initial
  have hsize : PolyBounded (fun q => (encQ q).length) (fun q => 3 * B q + 1) :=
    ((PolyBounded.const 3).mul hB).add (PolyBounded.const 1)
  exact RecursiveStack.evaluator (F := Frame Q S) (encF := encPair encQ encS)
    (value := fun f => answer f.1) (start := fun q => (q, C.initial q))
    (C.instruction_computable hC) (C.receive_computable hC) hi hN hR hsize
    (fun root => C.rules answer rank (tasks root) budget (N root) (hstop root) (hb root) (hdone root) (hquery root))
    (fun q => C.valid_initial answer (tasks q) budget q (hroot q))
    (fun root f hf => hrank root f.1 hf.1)
    (fun root f hf => by
      obtain ⟨hq, t, ht, he⟩ := hf
      have hq' := htask root f.1 hq
      have hs' := hstate root f.1 hq t ht
      rw [← he] at hs'
      simp only [length_encPair]
      omega)
    (fun root f hf => by have h := hanswer root f.1 hf.1; omega)

end LeanCanny.Computation.RecursiveController.Controller

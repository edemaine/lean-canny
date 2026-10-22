/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.RecursiveControllerSpace

/-! # Native dispatch between resumable controllers

The selected branch keeps its own state type. The inactive branch stores a
fixed default. Queries remain in one shared task type, so they may cross stages.
-/

@[expose] public section

namespace LeanCanny.Computation.RecursiveController.Controller
open Turing.MultiTapeTM

variable {Q A B : Type}

abbrev ChoiceState (A B : Type) := Bool × A × B
abbrev encChoice (eA : A ↪ List Bool) (eB : B ↪ List Bool) : ChoiceState A B ↪ List Bool :=
  encPair encBool (encPair eA eB)

def choose [Inhabited A] [Inhabited B] (select : Q → Bool) (C : Controller Q A) (D : Controller Q B) :
    Controller Q (ChoiceState A B) where
  initial := fun q => if select q then (true, C.initial q, default) else (false, default, D.initial q)
  halted := fun s => if s.1 then C.halted s.2.1 else D.halted s.2.2
  output := fun s => if s.1 then C.output s.2.1 else D.output s.2.2
  needs := fun s => if s.1 then C.needs s.2.1 else D.needs s.2.2
  query := fun s => if s.1 then C.query s.2.1 else D.query s.2.2
  advance := fun s => if s.1 then (true, C.advance s.2.1, s.2.2) else (false, s.2.1, D.advance s.2.2)
  resume := fun p => if p.1.1 then (true, C.resume (p.1.2.1, p.2), p.1.2.2)
    else (false, p.1.2.1, D.resume (p.1.2.2, p.2))

variable [Inhabited A] [Inhabited B] (select : Q → Bool) (C : Controller Q A) (D : Controller Q B)

theorem choose_reference_true (answer : Q → List Bool) (a : A) (b : B) :
    (choose select C D).reference answer (true, a, b) = (true, C.reference answer a, b) := by
  cases hh : C.halted a <;> cases hn : C.needs a <;>
    simp only [reference, choose, hh, hn, ite_true, Bool.false_eq_true, ite_false]

theorem choose_reference_false (answer : Q → List Bool) (a : A) (b : B) :
    (choose select C D).reference answer (false, a, b) = (false, a, D.reference answer b) := by
  cases hh : D.halted b <;> cases hn : D.needs b <;>
    simp only [reference, choose, hh, hn, ite_true, Bool.false_eq_true, ite_false]

theorem choose_iterate_true (answer : Q → List Bool) (a : A) (b : B) (t : ℕ) :
    ((choose select C D).reference answer)^[t] (true, a, b) = (true, (C.reference answer)^[t] a, b) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, choose_reference_true, Function.iterate_succ_apply']

theorem choose_iterate_false (answer : Q → List Bool) (a : A) (b : B) (t : ℕ) :
    ((choose select C D).reference answer)^[t] (false, a, b) = (false, a, (D.reference answer)^[t] b) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, choose_reference_false, Function.iterate_succ_apply']

theorem choose_observe_iterate {O : Type} (f : A → O) (g : B → O) (answer : Q → List Bool) (q : Q) (t : ℕ) :
    (let s := ((choose select C D).reference answer)^[t] ((choose select C D).initial q)
     if s.1 then f s.2.1 else g s.2.2) =
      if select q then f ((C.reference answer)^[t] (C.initial q)) else g ((D.reference answer)^[t] (D.initial q)) := by
  cases hs : select q with
  | true =>
    have hi : (choose select C D).initial q = (true, C.initial q, default) := by simp only [choose, hs, ite_true]
    rw [hi, choose_iterate_true]
    rfl
  | false =>
    have hi : (choose select C D).initial q = (false, default, D.initial q) := by
      simp only [choose, hs, Bool.false_eq_true, ite_false]
    rw [hi, choose_iterate_false]
    rfl

theorem choose_halted_iterate (answer : Q → List Bool) (q : Q) (t : ℕ) :
    (choose select C D).halted (((choose select C D).reference answer)^[t] ((choose select C D).initial q)) =
      if select q then C.halted ((C.reference answer)^[t] (C.initial q))
      else D.halted ((D.reference answer)^[t] (D.initial q)) :=
  choose_observe_iterate select C D C.halted D.halted answer q t

theorem choose_output_iterate (answer : Q → List Bool) (q : Q) (t : ℕ) :
    (choose select C D).output (((choose select C D).reference answer)^[t] ((choose select C D).initial q)) =
      if select q then C.output ((C.reference answer)^[t] (C.initial q))
      else D.output ((D.reference answer)^[t] (D.initial q)) :=
  choose_observe_iterate select C D C.output D.output answer q t

theorem choose_needs_iterate (answer : Q → List Bool) (q : Q) (t : ℕ) :
    (choose select C D).needs (((choose select C D).reference answer)^[t] ((choose select C D).initial q)) =
      if select q then C.needs ((C.reference answer)^[t] (C.initial q))
      else D.needs ((D.reference answer)^[t] (D.initial q)) :=
  choose_observe_iterate select C D C.needs D.needs answer q t

theorem choose_query_iterate (answer : Q → List Bool) (q : Q) (t : ℕ) :
    (choose select C D).query (((choose select C D).reference answer)^[t] ((choose select C D).initial q)) =
      if select q then C.query ((C.reference answer)^[t] (C.initial q))
      else D.query ((D.reference answer)^[t] (D.initial q)) :=
  choose_observe_iterate select C D C.query D.query answer q t

theorem encChoice_length {A B : Type} (eA : A ↪ List Bool) (eB : B ↪ List Bool)
    (flag : Bool) (a : A) (b : B) :
    (encChoice eA eB (flag, a, b)).length = 4 + 2 * (eA a).length + (eB b).length := by
  simp only [encChoice, length_encPair, encBool_apply, List.length_singleton]
  omega

theorem choose_encoded_length {A B : Type} [Inhabited A] [Inhabited B]
    (eA : A ↪ List Bool) (eB : B ↪ List Bool) (select : Q → Bool)
    (C : RecursiveController.Controller Q A) (D : RecursiveController.Controller Q B)
    (g : Q → List Bool) (q : Q) (t : ℕ) :
    (encChoice eA eB (((choose select C D).reference g)^[t] ((choose select C D).initial q))).length =
      if select q then 4 + 2 * (eA ((C.reference g)^[t] (C.initial q))).length + (eB default).length
      else 4 + 2 * (eA default).length + (eB ((D.reference g)^[t] (D.initial q))).length := by
  cases hs : select q with
  | true =>
    have hi : (choose select C D).initial q = (true, C.initial q, default) := by simp only [choose, hs, ite_true]
    rw [hi, choose_iterate_true]
    simp only [ite_true, encChoice, length_encPair, encBool_apply, List.length_singleton]
    omega
  | false =>
    have hi : (choose select C D).initial q = (false, default, D.initial q) := by
      simp only [choose, hs, Bool.false_eq_true, ite_false]
    rw [hi, choose_iterate_false]
    simp only [Bool.false_eq_true, ite_false, encChoice, length_encPair, encBool_apply, List.length_singleton]
    omega

theorem choose_state_length (eA : A ↪ List Bool) (eB : B ↪ List Bool)
    (answer : Q → List Bool) (q : Q) (t L : ℕ)
    (hA : select q = true → (eA ((C.reference answer)^[t] (C.initial q))).length ≤ L)
    (hB : select q = false → (eB ((D.reference answer)^[t] (D.initial q))).length ≤ L) :
    (encChoice eA eB (((choose select C D).reference answer)^[t] ((choose select C D).initial q))).length ≤
      4 + 2 * L + 2 * (eA default).length + (eB default).length := by
  rw [choose_encoded_length]
  cases hs : select q with
  | true => simp only [ite_true]; have h := hA hs; omega
  | false => simp only [Bool.false_eq_true, ite_false]; have h := hB hs; omega

variable {eQ : Q ↪ List Bool} {eA : A ↪ List Bool} {eB : B ↪ List Bool}

theorem choose_certificates (hs : ComputableTidilyInPolyTime select eQ encBool)
    (hC : C.Certificates (encQ := eQ) (encS := eA)) (hD : D.Certificates (encQ := eQ) (encS := eB)) :
    (choose select C D).Certificates (encQ := eQ) (encS := encChoice eA eB) := by
  rcases hC with ⟨hCi, hCh, hCo, hCn, hCq, hCa, hCr⟩
  rcases hD with ⟨hDi, hDh, hDo, hDn, hDq, hDa, hDr⟩
  constructor <;> dsimp only [choose, encChoice] <;> fun_prop (config := { maxSteps := 256 })

def prepare {S : Type} (E : Controller Q S) (input : Q → Q) : Controller Q S :=
  { E with initial := E.initial ∘ input }

theorem prepare_orbit {S : Type}
    (C : Controller Q S) (input : Q → Q) (g : Q → List Bool) (q : Q) (t : ℕ) :
    ((prepare C input).reference g)^[t] ((prepare C input).initial q) =
      (C.reference g)^[t] (C.initial (input q)) := rfl

theorem prepare_halted_iterate {S : Type} (E : Controller Q S) (input : Q → Q)
    (answer : Q → List Bool) (q : Q) (t : ℕ) :
    (prepare E input).halted (((prepare E input).reference answer)^[t] ((prepare E input).initial q)) =
      E.halted ((E.reference answer)^[t] (E.initial (input q))) := rfl

theorem prepare_output_iterate {S : Type} (E : Controller Q S) (input : Q → Q)
    (answer : Q → List Bool) (q : Q) (t : ℕ) :
    (prepare E input).output (((prepare E input).reference answer)^[t] ((prepare E input).initial q)) =
      E.output ((E.reference answer)^[t] (E.initial (input q))) := rfl

theorem prepare_needs_iterate {S : Type} (E : Controller Q S) (input : Q → Q)
    (answer : Q → List Bool) (q : Q) (t : ℕ) :
    (prepare E input).needs (((prepare E input).reference answer)^[t] ((prepare E input).initial q)) =
      E.needs ((E.reference answer)^[t] (E.initial (input q))) := rfl

theorem prepare_query_iterate {S : Type} (E : Controller Q S) (input : Q → Q)
    (answer : Q → List Bool) (q : Q) (t : ℕ) :
    (prepare E input).query (((prepare E input).reference answer)^[t] ((prepare E input).initial q)) =
      E.query ((E.reference answer)^[t] (E.initial (input q))) := rfl

theorem prepare_certificates {S : Type} {eS : S ↪ List Bool} (E : Controller Q S) (input : Q → Q)
    (hE : E.Certificates (encQ := eQ) (encS := eS)) (hi : ComputableTidilyInPolyTime input eQ eQ) :
    (prepare E input).Certificates (encQ := eQ) (encS := eS) :=
  ⟨hE.initial.comp (.of_polyTime hi), hE.halted, hE.output, hE.needs, hE.query, hE.advance, hE.resume⟩

end LeanCanny.Computation.RecursiveController.Controller

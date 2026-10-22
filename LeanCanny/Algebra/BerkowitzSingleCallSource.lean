/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzTaskLevels

/-! # Closing a determinant graph with a one-request source

Query closure bounds the source's sole stored reply. This applies equally to
native leaf computations and recursive resultant entries, with logical budget
one and state bound `3*K+4`. Output processing may take arbitrary time.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
open LeanCanny.Encoding LeanCanny.Computation
open Turing.MultiTapeTM

variable {F : ModularFamily} (a : ModularAccess F) (P : SingleCall.Program)
attribute [local irreducible] isZero isDeterminant isFactor isMoment payload

theorem singleCall_source_levels (tasks : List Bool → List Bool → Prop) (level : List Bool → ℕ)
    (h : ∀ p, P.request p = true → isZero (P.query p) = false →
      level (origin (P.query p)) < level (pairFst p)) :
    SourceLevels a P.controller (fun _ => 1) tasks level := by
  intro root q t hq hs ht hh hn hz
  change P.request (((P.controller.reference (answer a))^[t] (SingleCall.Program.initial (payload q))).1) = true at hn
  change isZero (P.query (((P.controller.reference (answer a))^[t] (SingleCall.Program.initial (payload q))).1)) = false at hz
  change level (origin (P.query (((P.controller.reference (answer a))^[t]
    (SingleCall.Program.initial (payload q))).1))) < level (origin q)
  rw [P.context_iterate] at hn hz ⊢
  rcases hs with ⟨h0, hd, hf, hm⟩
  simpa only [origin, h0, hd, hf, hm, Bool.false_eq_true, ite_false] using h (payload q) hn hz

theorem singleCall_source_state_bound (tasks : List Bool → List Bool → Prop)
    (hclosed : QueriesClosed a P.controller (fun _ => 1) tasks) (K : List Bool → ℕ)
    (hword : ∀ root q, tasks root q → q.length ≤ K root)
    (hanswer : ∀ root q, tasks root q → (answer a q).length ≤ K root)
    (root q : List Bool) (hq : tasks root q) (hs : SelectedSource q) (t : ℕ) :
    (SingleCall.encState ((P.controller.reference (answer a))^[t]
      (SingleCall.Program.initial (payload q)))).length ≤ 3 * K root + 4 := by
  have hp : (payload q).length ≤ q.length := by simp only [payload, List.length_drop]; omega
  have hw := hp.trans (hword root q hq)
  have hb : P.request (payload q) = true → (answer a (P.query (payload q))).length ≤ K root := by
    intro hn
    rcases hs with ⟨hz, hd, hf, hm⟩
    have hh : (controller a P.controller).halted
        (((controller a P.controller).reference (answer a))^[0] ((controller a P.controller).initial q)) = false := by
      rw [halted_iterate]
      simp only [hz, hd, hf, hm, Bool.false_eq_true, ite_false, Function.iterate_zero, id_eq]
      change Bool.not (P.request (payload q)) = false
      rw [hn]; rfl
    have hn' : (controller a P.controller).needs
        (((controller a P.controller).reference (answer a))^[0] ((controller a P.controller).initial q)) = true := by
      rw [needs_iterate]
      simpa only [hz, hd, hf, hm, Bool.false_eq_true, ite_false, Function.iterate_zero, id_eq,
        SingleCall.Program.controller, SingleCall.Program.initial] using hn
    have hc := hclosed root q 0 hq (Nat.zero_le _) hh hn'
    rw [query_iterate] at hc
    simp only [hz, hd, hf, hm, Bool.false_eq_true, ite_false, Function.iterate_zero, id_eq,
      SingleCall.Program.controller, SingleCall.Program.initial] at hc
    exact hanswer root _ hc
  have h := P.state_length_of_bound (answer a) (payload q) t (K root) hb
  omega

theorem singleCall_evaluator (ha : a.ControlsPolyTime)
    (hP : P.controller.Certificates (encQ := encBits) (encS := SingleCall.encState))
    (hcorrect : ∀ p, P.value (answer a) p = a.entry p)
    (tasks : List Bool → List Bool → Prop) (level H K M : List Bool → ℕ)
    (hH : UnaryFn H) (hK : UnaryFn K) (hM : UnaryFn M)
    (hroot : ∀ q, tasks q q)
    (hlevels : ∀ root q, tasks root q → level (origin q) ≤ H root)
    (hword : ∀ root q, tasks root q → q.length ≤ K root)
    (hanswer : ∀ root q, tasks root q → (answer a q).length ≤ K root)
    (hclosed : QueriesClosed a P.controller (fun _ => 1) tasks)
    (hlevel : SourceLevels a P.controller (fun _ => 1) tasks level)
    (hdet : ∀ root q, tasks root q → SelectedDeterminant q → determinantFields (F := F) (payload q) ≤ M root)
    (hmoment : ∀ root q, tasks root q → SelectedMoment q → momentFields (F := F) (payload q) ≤ M root) :
    SpaceFunction (answer a) :=
  evaluator_of_source_levels a P.controller ha hP (fun _ => 1) (P.halted_after (answer a))
    (fun p t hh => (P.output_when_halted (answer a) p t hh).trans (hcorrect p))
    tasks level H K M (fun root => 3 * K root + 4) (fun _ => 1) hH hK hM
    (((UnaryFn.const 3).mul hK).add (UnaryFn.const 4)) (BinaryFn.const 1)
    hroot hlevels hword hanswer hclosed hlevel hdet hmoment (fun _ _ _ _ => Nat.le_refl 1)
    (fun root q hq hs t _ => singleCall_source_state_bound a P tasks hclosed K hword hanswer root q hq hs t)

end LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch

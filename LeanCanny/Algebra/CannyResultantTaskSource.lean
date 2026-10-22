/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyResultantRecursiveStage
public import LeanCanny.Algebra.BerkowitzTaskLevels

/-! # Canny's resultant-entry source in the recursive determinant graph

The concrete source has logical budget one. Query closure bounds its sole
stored reply, giving source-state size `3*K+4` from the common task/reply bound
K. Local binomial postprocessing is supplied by the native space calculus.
Only the original-polynomial task writers need child-level decrease proofs.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyResultantBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation
open Turing.MultiTapeTM
open BerkowitzPolynomial.TaskDispatch

variable {F : Family} (a : Access F) (leftTask rightTask : List Bool → List Bool)

attribute [local irreducible] isZero isDeterminant isFactor isMoment payload
  BinaryNat.normalize BinaryNat.add BinaryNat.sub BinaryNat.mul BinaryNat.mulMod BinaryNat.powMod
  selectRight request leftQuery rightQuery

theorem source_levels (tasks : List Bool → List Bool → Prop) (level : List Bool → ℕ)
    (hl : ∀ p, request a p = true → selectRight a p = false → isZero (leftTask (leftQuery a p)) = false →
      level (origin (leftTask (leftQuery a p))) < level (pairFst p))
    (hr : ∀ p, request a p = true → selectRight a p = true → isZero (rightTask (rightQuery p)) = false →
      level (origin (rightTask (rightQuery p))) < level (pairFst p)) :
    SourceLevels a.modular.determinant (program a leftTask rightTask).controller (fun _ => 1) tasks level := by
  intro root q t hq hs ht hh hn hz
  change (program a leftTask rightTask).controller.needs
    (((program a leftTask rightTask).controller.reference (answer a.modular.determinant))^[t]
      (SingleCall.Program.initial (payload q))) = true at hn
  change isZero ((program a leftTask rightTask).controller.query
    (((program a leftTask rightTask).controller.reference (answer a.modular.determinant))^[t]
      (SingleCall.Program.initial (payload q)))) = false at hz
  change level (origin ((program a leftTask rightTask).controller.query
    (((program a leftTask rightTask).controller.reference (answer a.modular.determinant))^[t]
      (SingleCall.Program.initial (payload q))))) < level (origin q)
  rw [needs_iterate] at hn
  rw [query_iterate] at hz ⊢
  have ho : origin q = pairFst (payload q) := by
    rcases hs with ⟨h0, hd, hf, hm⟩
    simp only [origin, h0, hd, hf, hm, Bool.false_eq_true, ite_false]
  rw [ho]
  cases hsel : selectRight a (payload q) with
  | true =>
    simp only [hsel, ite_true] at hz ⊢
    exact hr _ hn hsel hz
  | false =>
    simp only [hsel, Bool.false_eq_true, ite_false] at hz ⊢
    exact hl _ hn hsel hz

theorem source_state_bound (tasks : List Bool → List Bool → Prop)
    (hclosed : QueriesClosed a.modular.determinant (program a leftTask rightTask).controller (fun _ => 1) tasks)
    (K : List Bool → ℕ)
    (hword : ∀ root q, tasks root q → q.length ≤ K root)
    (hanswer : ∀ root q, tasks root q → (answer a.modular.determinant q).length ≤ K root)
    (root q : List Bool) (hq : tasks root q) (hs : SelectedSource q) (t : ℕ) :
    (SingleCall.encState (((program a leftTask rightTask).controller.reference (answer a.modular.determinant))^[t]
      (SingleCall.Program.initial (payload q)))).length ≤ 3 * K root + 4 := by
  have hp : (payload q).length ≤ q.length := by
    simp only [payload, List.length_drop]
    omega
  have hw := hp.trans (hword root q hq)
  have hb : request a (payload q) = true →
      (answer a.modular.determinant ((program a leftTask rightTask).query (payload q))).length ≤ K root := by
    intro hn
    rcases hs with ⟨hz, hd, hf, hm⟩
    have hh : (BerkowitzPolynomial.TaskDispatch.controller a.modular.determinant (program a leftTask rightTask).controller).halted
        (((BerkowitzPolynomial.TaskDispatch.controller a.modular.determinant (program a leftTask rightTask).controller).reference
          (answer a.modular.determinant))^[0]
          ((BerkowitzPolynomial.TaskDispatch.controller a.modular.determinant (program a leftTask rightTask).controller).initial q)) = false := by
      rw [halted_iterate]
      simp only [hz, hd, hf, hm, Bool.false_eq_true, ite_false, Function.iterate_zero, id_eq,
        SingleCall.Program.controller, SingleCall.Program.initial, program, hn, Bool.not_true]
    have hn' : (BerkowitzPolynomial.TaskDispatch.controller a.modular.determinant (program a leftTask rightTask).controller).needs
        (((BerkowitzPolynomial.TaskDispatch.controller a.modular.determinant (program a leftTask rightTask).controller).reference
          (answer a.modular.determinant))^[0]
          ((BerkowitzPolynomial.TaskDispatch.controller a.modular.determinant (program a leftTask rightTask).controller).initial q)) = true := by
      rw [BerkowitzPolynomial.TaskDispatch.needs_iterate]
      simp only [hz, hd, hf, hm, Bool.false_eq_true, ite_false, Function.iterate_zero, id_eq,
        SingleCall.Program.controller, SingleCall.Program.initial, program, hn]
    have hc := hclosed root q 0 hq (Nat.zero_le _) hh hn'
    rw [BerkowitzPolynomial.TaskDispatch.query_iterate] at hc
    simp only [hz, hd, hf, hm, Bool.false_eq_true, ite_false, Function.iterate_zero, id_eq,
      SingleCall.Program.controller, SingleCall.Program.initial] at hc
    exact hanswer root _ hc
  have h := (program a leftTask rightTask).state_length_of_bound (answer a.modular.determinant)
    (payload q) t (K root) hb
  omega

/-- Uniform native coefficient access for this concrete Canny source stage.
Child semantics, source-level decreases, query closure, and common task and
metadata bounds remain explicit. No original-coefficient space certificate is
assumed. -/
theorem evaluator (ha : a.ControlsPolyTime) (hlFP : leftTask ∈ FP) (hrFP : rightTask ∈ FP)
    (hl : ∀ p, answer a.modular.determinant (leftTask p) = a.leftCoefficient p)
    (hr : ∀ p, answer a.modular.determinant (rightTask p) = a.rightCoefficient p)
    (tasks : List Bool → List Bool → Prop) (level H K M : List Bool → ℕ)
    (hH : UnaryFn H) (hK : UnaryFn K) (hM : UnaryFn M)
    (hroot : ∀ q, tasks q q)
    (hlevels : ∀ root q, tasks root q → level (origin q) ≤ H root)
    (hword : ∀ root q, tasks root q → q.length ≤ K root)
    (hanswer : ∀ root q, tasks root q → (answer a.modular.determinant q).length ≤ K root)
    (hclosed : QueriesClosed a.modular.determinant (program a leftTask rightTask).controller (fun _ => 1) tasks)
    (hlevel : SourceLevels a.modular.determinant (program a leftTask rightTask).controller (fun _ => 1) tasks level)
    (hdet : ∀ root q, tasks root q → SelectedDeterminant q →
      determinantFields (F := F.modular.determinant) (payload q) ≤ M root)
    (hmoment : ∀ root q, tasks root q → SelectedMoment q →
      momentFields (F := F.modular.determinant) (payload q) ≤ M root) : SpaceFunction F.value := by
  have E := evaluator_of_source_levels a.modular.determinant (program a leftTask rightTask).controller
    (a.modular.determinant_controls (a.modular_controlsWithCoefficients ha)) (certificates a ha leftTask rightTask hlFP hrFP)
    (fun _ => 1) (halted_after a leftTask rightTask (answer a.modular.determinant))
    (output_when_halted a leftTask rightTask (answer a.modular.determinant) hl hr)
    tasks level H K M (fun root => 3 * K root + 4) (fun _ => 1) hH hK hM
    (((UnaryFn.const 3).mul hK).add (UnaryFn.const 4)) (BinaryFn.const 1)
    hroot hlevels hword hanswer hclosed hlevel hdet hmoment (fun _ _ _ _ => Nat.le_refl 1)
    (fun root q hq hs t _ => source_state_bound a leftTask rightTask tasks hclosed K hword hanswer root q hq hs t)
  exact (determinant_reader a.modular.determinant E).congr (funext F.modular_value)

end LeanCanny.Algebra.CannyResultantBits.RecursiveStage

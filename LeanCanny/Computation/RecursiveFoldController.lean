/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.ControllerRequests
public import LeanCanny.Computation.BoundedFoldSpace
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Resumable binary folds with recursively requested entries

A controller keeps one context, one binary counter, and one accumulator.
A child request suspends the fold; no certificate for the child answer
routine is assumed. The same controller covers modular sums and products
when their usual FP finish operations bound the accumulator.
-/

@[expose] public section
namespace LeanCanny.Computation.RecursiveFold
open LeanCanny.Encoding Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

abbrev State := List Bool × ℕ × List Bool
abbrev encState : State ↪ List Bool := encPair encBits (encPair encNat encBits)

structure Program where
  count : List Bool → ℕ
  seed : List Bool → List Bool
  entryTask : List Bool → List Bool
  finish : List Bool → List Bool

namespace Program
variable (P : Program)

def initial (q : List Bool) : State := (q, 0, P.seed q)
def child (q : List Bool) (i : ℕ) : List Bool := P.entryTask (pair q (BinaryNatCode.encode i))
def controller : RecursiveController.Controller (List Bool) State where
  initial := initial P
  halted s := decide (P.count s.1 ≤ s.2.1)
  output s := s.2.2
  needs _ := true
  query s := P.child s.1 s.2.1
  advance := id
  resume p := (p.1.1, p.1.2.1 + 1, P.finish (pair (BoundedFold.packet p.1.1 p.1.2.1 p.1.2.2) p.2))

def update (answer : List Bool → List Bool) : List Bool → List Bool :=
  BoundedFold.update P.finish (answer ∘ P.entryTask)
def partialValue (answer : List Bool → List Bool) (q : List Bool) (i : ℕ) : List Bool :=
  BoundedFold.fold (P.update answer) P.seed q i

def value (answer : List Bool → List Bool) (q : List Bool) : List Bool := P.partialValue answer q (P.count q)

theorem reference_step (answer : List Bool → List Bool) (q : List Bool) (i : ℕ) (v : List Bool)
    (hi : i < P.count q) : P.controller.reference answer (q, i, v) =
      (q, i + 1, P.update answer (BoundedFold.packet q i v)) := by
  simp only [RecursiveController.Controller.reference, controller, not_le.mpr hi, decide_false,
    Bool.false_eq_true, ite_false, ite_true, child, update, BoundedFold.update, BoundedFold.query,
    BoundedFold.context_packet, BoundedFold.counter_packet, Function.comp_apply]

theorem reference_final (answer : List Bool → List Bool) (q : List Bool) (v : List Bool) :
    P.controller.reference answer (q, P.count q, v) = (q, P.count q, v) := by
  simp only [RecursiveController.Controller.reference, controller, le_refl, decide_true, ite_true]

theorem reference_iterate (answer : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    (P.controller.reference answer)^[t] (P.initial q) =
      (q, min t (P.count q), P.partialValue answer q (min t (P.count q))) := by
  induction t with
  | zero => simp only [Function.iterate_zero, id_eq, initial, Nat.zero_min, partialValue, BoundedFold.fold]
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases ht : t < P.count q
    · rw [min_eq_left ht.le, min_eq_left (Nat.succ_le_of_lt ht), P.reference_step answer q t _ ht]
      rfl
    · have ht' : P.count q ≤ t := by omega
      rw [min_eq_right ht', min_eq_right (by omega : P.count q ≤ t + 1), P.reference_final]

theorem halted_after (answer : List Bool → List Bool) (q : List Bool) :
    P.controller.halted ((P.controller.reference answer)^[P.count q] (P.initial q)) = true := by
  rw [P.reference_iterate, min_self]
  simp only [controller, le_refl, decide_true]

theorem output_when_halted (answer : List Bool → List Bool) (q : List Bool) (t : ℕ)
    (hh : P.controller.halted ((P.controller.reference answer)^[t] (P.initial q)) = true) :
    P.controller.output ((P.controller.reference answer)^[t] (P.initial q)) = P.value answer q := by
  rw [P.reference_iterate] at hh ⊢
  have HE : min t (P.count q) = P.count q := by
    have H : P.count q ≤ min t (P.count q) := of_decide_eq_true hh
    omega
  rw [HE]
  rfl

theorem requests_iff (answer : List Bool → List Bool) (q r : List Bool) :
    P.controller.Requests answer P.count q r ↔ ∃ i < P.count q, r = P.child q i := by
  simp only [RecursiveController.Controller.Requests, show P.controller.initial = P.initial from rfl]
  constructor
  · rintro ⟨t, ht, hh, _hn, he⟩
    rw [P.reference_iterate, min_eq_left ht] at hh he
    have HL : t < P.count q := by
      have H : ¬ P.count q ≤ t := of_decide_eq_false hh
      omega
    exact ⟨t, HL, he⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, hi.le, ?_, rfl, ?_⟩
    · rw [P.reference_iterate, min_eq_left hi.le]
      simp only [controller, not_le.mpr hi, decide_false]
    · rw [P.reference_iterate, min_eq_left hi.le]
      rfl

theorem state_length (q : List Bool) (i : ℕ) (v : List Bool) :
    (encState (q, i, v)).length = 2 * q.length + 2 * (encNat i).length + v.length + 2 := by
  simp only [encState, length_encPair, encBits_apply]
  omega

theorem orbit_length (answer : List Bool → List Bool) (q : List Bool) (t B : ℕ)
    (hB : ∀ i ≤ P.count q, (P.partialValue answer q i).length ≤ B) :
    (encState ((P.controller.reference answer)^[t] (P.initial q))).length ≤
      2 * q.length + 2 * (encNat (P.count q)).length + B + 2 := by
  rw [P.reference_iterate, state_length]
  have HI := ComputableTidilyInO.length_encNat_mono (min_le_right t (P.count q))
  have HV := hB (min t (P.count q)) (min_le_right _ _)
  omega

theorem certificates (hc : BinaryFn P.count) (hs : P.seed ∈ FP)
    (he : P.entryTask ∈ FP) (hf : P.finish ∈ FP) :
    P.controller.Certificates (encQ := encBits) (encS := encState) := by
  have hcount := ComputableTidilyInPolySpace.of_polyTime hc
  have hseed := ComputableTidilyInPolySpace.of_polyTime (FP.computable hs)
  have hentry := ComputableTidilyInPolySpace.of_polyTime (FP.computable he)
  have hfinish := ComputableTidilyInPolySpace.of_polyTime (FP.computable hf)
  have hbits : ComputableTidilyInPolySpace BinaryNatCode.encode encNat encBits := .of_polyTime natBits_computable
  have hpacket := ComputableTidilyInPolySpace.of_polyTime BoundedFold.packet_polyTime
  constructor
  · change ComputableTidilyInPolySpace (fun q : List Bool => (q, 0, P.seed q)) _ _
    fun_prop (config := { maxSteps := 256, maxTransitionDepth := 2 })
  all_goals dsimp only [controller, child, encState]
  all_goals fun_prop (config := { maxSteps := 256, maxTransitionDepth := 2 })

end Program
end LeanCanny.Computation.RecursiveFold

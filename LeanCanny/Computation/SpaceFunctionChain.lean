/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFoldSpace
public import LeanCanny.Computation.SpaceFunctionBranch

/-!
# Sequential composition of certified space-bounded output routines

The first routine's output has polynomial length because both its final state
and FP output projection do. A two-update suspended fold runs the first routine
and then the second. All saved inputs, intermediate output, and child states
are included in the bounded-fold certificate.
-/

@[expose] public section

namespace LeanCanny.Computation.SpaceFunction
open Complexity
open LeanCanny.Encoding

theorem exists_output_length_poly {f : List Bool → List Bool} (E : SpaceFunction f) :
    ∃ p : Polynomial ℕ, ∀ x, (f x).length ≤ p.eval x.length := by
  obtain ⟨q, hq⟩ := Cobham.output_length_poly_of_mem_FP E.outputFP
  refine ⟨q.comp E.space, ?_⟩
  intro x
  rw [← E.correct x]
  have h := (hq _).trans (polynomial_eval_mono_nat q (E.length_le x (E.time x) le_rfl))
  simpa only [Polynomial.eval_comp] using h

def firstUpdate (p : List Bool) : Bool := decide (Nat.fromBitsLE (BoundedFold.counter p) < 1)

def chainUpdate (f g : List Bool → List Bool) (p : List Bool) : List Bool :=
  if firstUpdate p then f (pairFst p) else g (BoundedFold.accumulator p)

theorem firstUpdate_mem_FP : (fun p => [firstUpdate p]) ∈ FP :=
  (BinaryNat.lt_fppred BoundedFold.counter_mem_FP (constFn_mem_FP [true])).flag_mem_FP

theorem chain_one (f g : List Bool → List Bool) (c : List Bool) :
    BoundedFold.fold (chainUpdate f g) (fun _ => []) c 1 = f c := by
  simp only [BoundedFold.fold, chainUpdate, firstUpdate, BoundedFold.counter_packet,
    BoundedFold.context_packet, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.zero_lt_one,
    decide_true, ↓reduceIte]

theorem chain_two (f g : List Bool → List Bool) (c : List Bool) :
    BoundedFold.fold (chainUpdate f g) (fun _ => []) c 2 = g (f c) := by
  change chainUpdate f g (BoundedFold.packet c 1 (BoundedFold.fold (chainUpdate f g) (fun _ => []) c 1)) = _
  rw [chain_one]
  simp only [chainUpdate, firstUpdate, BoundedFold.counter_packet, BoundedFold.accumulator_packet,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, lt_self_iff_false, decide_false, Bool.false_eq_true, ↓reduceIte]

noncomputable def chain {f g : List Bool → List Bool} (E : SpaceFunction f) (G : SpaceFunction g) :
    SpaceFunction (g ∘ f) := by
  have EC : SpaceFunction (chainUpdate f g) :=
    branch firstUpdate firstUpdate_mem_FP (E.precompose pairFst pairFst_mem_FP)
      (G.precompose BoundedFold.accumulator BoundedFold.accumulator_mem_FP)
  let p := Classical.choose E.exists_output_length_poly
  have hp : ∀ x, (f x).length ≤ p.eval x.length := Classical.choose_spec E.exists_output_length_poly
  let q := Classical.choose G.exists_output_length_poly
  have hq : ∀ x, (g x).length ≤ q.eval x.length := Classical.choose_spec G.exists_output_length_poly
  let s := p + q.comp p + 1
  have hs : ∀ c i, i ≤ Nat.fromBitsLE [false, true] →
      (BoundedFold.fold (chainUpdate f g) (fun _ => []) c i).length ≤ s.eval c.length := by
    intro c i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by change i ≤ 2 at hi; omega
    rcases hi' with rfl | rfl | rfl
    · simp only [BoundedFold.fold, List.length_nil]
      exact Nat.zero_le _
    · rw [chain_one]
      have h := hp c
      simp only [s, Polynomial.eval_add, Polynomial.eval_one]
      omega
    · rw [chain_two]
      have h := (hq (f c)).trans (polynomial_eval_mono_nat q (hp c))
      change (g (f c)).length ≤ q.eval (p.eval c.length) at h
      simp only [s, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_comp]
      omega
  let R := BoundedFold.evaluator EC (fun _ => [false, true]) (fun _ => [])
    (constFn_mem_FP [false, true]) (constFn_mem_FP []) s hs
  refine R.congr (funext fun c => ?_)
  exact chain_two f g c

end LeanCanny.Computation.SpaceFunction

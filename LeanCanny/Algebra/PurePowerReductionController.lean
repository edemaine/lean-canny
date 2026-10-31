/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PurePowerReductionSpace
public import LeanCanny.Computation.ControllerRequests

/-! # Resumable pure-power reduction entries

Diagonal normal entries use the local integer-leading reader. A valid
nonnormal entry requests one shifted lower coefficient and negates it.
All other entries return zero. Child evaluators are absent from the local
native certificate, including after FP preparation of the input packet.
-/

@[expose] public section
namespace LeanCanny.Algebra.PurePowerReductionBits
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] negate sourceQuery

def request (L : Layout) (bound : List Bool → ℕ) (p : List Bool) : Prop :=
  ¬ normal L p ∧ valid L bound p ∧ admissible L p

def immediate (L : Layout) (constant : List Bool → List Bool) (p : List Bool) : List Bool :=
  if normal L p ∧ sameIndex p then constant (pairFst p) else []

def finish (input : List Bool → List Bool) (z : List Bool) : List Bool :=
  negate (pair (input (pairFst z)) (pairSnd z))

noncomputable def program (L : Layout) (bound : List Bool → ℕ)
    (constant input task : List Bool → List Bool) : SingleCall.Program where
  request p := decide (request L bound (input p))
  query p := task (sourceQuery L (input p))
  immediate p := immediate L constant (input p)
  finish := finish input

theorem request_FP (L : Layout) (h : L.PolyTime) (bound : List Bool → ℕ) (hb : BinaryFn bound) :
    FPPred (request L bound) := (normal_fppred h).not.and ((valid_fppred h hb).and (admissible_fppred h))

theorem immediate_FP (L : Layout) (h : L.PolyTime) (constant : List Bool → List Bool) (hc : constant ∈ FP) :
    immediate L constant ∈ FP :=
  ((normal_fppred h).and sameIndex_fppred).ite_mem_FP
    (mem_FP_comp pairFst_mem_FP hc) (constFn_mem_FP [])

theorem finish_FP (input : List Bool → List Bool) (hi : input ∈ FP) : finish input ∈ FP :=
  mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hi) pairSnd_mem_FP) negate_mem_FP

theorem program_controls (L : Layout) (h : L.PolyTime) (bound : List Bool → ℕ) (hb : BinaryFn bound)
    (constant input task : List Bool → List Bool) (hc : constant ∈ FP) (hi : input ∈ FP) (ht : task ∈ FP) :
    (program L bound constant input task).Controls where
  request := ((request_FP L h bound hb).comp hi).flag_mem_FP
  query := mem_FP_comp (f := fun p => sourceQuery L (input p)) (g := task)
    (mem_FP_comp (f := input) (g := sourceQuery L) hi (sourceQuery_mem_FP h)) ht
  immediate := mem_FP_comp (f := input) (g := immediate L constant) hi (immediate_FP L h constant hc)
  finish := finish_FP input hi

theorem program_value (L : Layout) (bound : List Bool → ℕ) (constant coefficient input task answer : List Bool → List Bool)
    (he : ∀ p, answer (task p) = coefficient p) (p : List Bool) :
    (program L bound constant input task).value answer p = entry L bound constant coefficient (input p) := by
  by_cases hn : normal L (input p)
  · simp only [SingleCall.Program.value, program, request, hn, not_true_eq_false, false_and,
      decide_false, Bool.false_eq_true, ite_false, immediate, true_and, entry, ite_true]
  · by_cases hv : valid L bound (input p)
    · by_cases ha : admissible L (input p)
      · have hr : request L bound (input p) := ⟨hn, hv, ha⟩
        simp only [SingleCall.Program.value, program, show decide (request L bound (input p)) = true from decide_eq_true hr,
          ite_true, finish, pairFst_pair, pairSnd_pair, he, entry, hn, ite_false, hv, ha]
      · have hr : ¬ request L bound (input p) := fun h => ha h.2.2
        simp only [SingleCall.Program.value, program, show decide (request L bound (input p)) = false from decide_eq_false hr,
          Bool.false_eq_true, ite_false, immediate, hn, false_and, entry, hv, ha, ite_true]
    · have hr : ¬ request L bound (input p) := fun h => hv h.2.1
      simp only [SingleCall.Program.value, program, show decide (request L bound (input p)) = false from decide_eq_false hr,
        Bool.false_eq_true, ite_false, immediate, hn, false_and, entry, hv]

theorem program_requests_iff (L : Layout) (bound : List Bool → ℕ) (constant input task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (p child : List Bool) :
    (program L bound constant input task).controller.Requests answer budget p child ↔
      request L bound (input p) ∧ child = task (sourceQuery L (input p)) := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

end LeanCanny.Algebra.PurePowerReductionBits

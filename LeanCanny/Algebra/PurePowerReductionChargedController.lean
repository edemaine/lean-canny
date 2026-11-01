/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PurePowerReductionController
/-! # Resumable reduction entries with a charged leading scalar

A normal diagonal entry requests its leading scalar instead of evaluating
it locally. Other nonzero entries retain their lower-coefficient request.
The native local certificate assumes no evaluator for either child.
-/
@[expose] public section
namespace LeanCanny.Algebra.PurePowerReductionBits.Charged
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] negate sourceQuery

def scalar (L : Layout) (p : List Bool) : Prop := normal L p ∧ sameIndex p

theorem scalar_FP (L : Layout) (h : L.PolyTime) : FPPred (scalar L) :=
  (normal_fppred h).and sameIndex_fppred

noncomputable def program (L : Layout) (bound : List Bool → ℕ)
    (input constantTask coefficientTask scalarFinish : List Bool → List Bool) : SingleCall.Program where
  request p := decide (scalar L (input p) ∨ request L bound (input p))
  query p := if scalar L (input p) then constantTask (pairFst (input p)) else coefficientTask (sourceQuery L (input p))
  immediate _ := []
  finish z := if scalar L (input (pairFst z)) then scalarFinish z else PurePowerReductionBits.finish input z

theorem controls (L : Layout) (h : L.PolyTime) (bound : List Bool → ℕ) (hb : BinaryFn bound)
    (input constantTask coefficientTask scalarFinish : List Bool → List Bool)
    (hi : input ∈ FP) (hc : constantTask ∈ FP) (he : coefficientTask ∈ FP) (hf : scalarFinish ∈ FP) :
    (program L bound input constantTask coefficientTask scalarFinish).Controls := by
  have HS := (scalar_FP L h).comp hi
  exact {
    request := (HS.or ((request_FP L h bound hb).comp hi)).flag_mem_FP
    query := HS.ite_mem_FP (mem_FP_comp (mem_FP_comp hi pairFst_mem_FP) hc)
      (mem_FP_comp (mem_FP_comp hi (sourceQuery_mem_FP h)) he)
    immediate := constFn_mem_FP []
    finish := (HS.comp pairFst_mem_FP).ite_mem_FP hf (finish_FP input hi) }

theorem value_at (L : Layout) (bound : List Bool → ℕ)
    (input constantTask coefficientTask scalarFinish constant coefficient answer : List Bool → List Bool)
    (p : List Bool)
    (hc : scalar L (input p) →
      scalarFinish (pair p (answer (constantTask (pairFst (input p))))) = constant (pairFst (input p)))
    (he : request L bound (input p) →
      answer (coefficientTask (sourceQuery L (input p))) = coefficient (sourceQuery L (input p))) :
    (program L bound input constantTask coefficientTask scalarFinish).value answer p =
      entry L bound constant coefficient (input p) := by
  by_cases hn : normal L (input p)
  · by_cases hs : sameIndex (input p)
    · have H : scalar L (input p) := ⟨hn, hs⟩
      simp only [SingleCall.Program.value, program, H, true_or, decide_true, ite_true,
        pairFst_pair, hc H, entry, hn, hs]
    · have H : ¬ scalar L (input p) := fun h => hs h.2
      have HR : ¬ request L bound (input p) := fun h => h.1 hn
      simp only [SingleCall.Program.value, program, H, HR, false_or, decide_false,
        Bool.false_eq_true, ite_false, entry, hn, hs, ite_true]
  · have H : ¬ scalar L (input p) := fun h => hn h.1
    by_cases hr : request L bound (input p)
    · simp only [SingleCall.Program.value, program, H, hr, or_true, decide_true, ite_true,
        ite_false, pairFst_pair, pairSnd_pair,
        PurePowerReductionBits.finish, he hr, entry, hn, hr.2.1, hr.2.2]
    · have HV : ¬ (valid L bound (input p) ∧ admissible L (input p)) := fun h => hr ⟨hn, h⟩
      simp only [SingleCall.Program.value, program, H, hr, false_or, decide_false,
        Bool.false_eq_true, ite_false, entry, hn]
      by_cases hv : valid L bound (input p)
      · rw [ite_eq_left hv, ite_eq_right (fun ha => HV ⟨hv, ha⟩)]
      · rw [ite_eq_right hv]

theorem requests_iff (L : Layout) (bound : List Bool → ℕ)
    (input constantTask coefficientTask scalarFinish answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (p child : List Bool) :
    (program L bound input constantTask coefficientTask scalarFinish).controller.Requests answer budget p child ↔
      (scalar L (input p) ∧ child = constantTask (pairFst (input p))) ∨
      (request L bound (input p) ∧ child = coefficientTask (sourceQuery L (input p))) := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]
  by_cases hs : scalar L (input p)
  · have HR : ¬ request L bound (input p) := fun h => h.1 hs.1
    simp only [hs, HR, true_and, false_and, or_false, ite_true]
  · simp only [hs, false_or, false_and, ite_false]

end LeanCanny.Algebra.PurePowerReductionBits.Charged

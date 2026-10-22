/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyBalancedTaskRanks

/-! # Active source requests and inherited context bounds

An active source request is nonleaf and passes the resultant entry guard.
Internal requests preserve the original context or request zero. These facts
propagate any context measure that does not increase on a nonleaf child.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyBalancedTaskRouting
open LeanCanny.Encoding LeanCanny.Computation
open BerkowitzPolynomial.TaskDispatch

variable (L : SeparableBits.Family) {F : CannyResultantBits.Family} {leftOrder rightOrder : List Bool → ℕ}
  (a : CannyResultantBits.Access F leftOrder rightOrder)

theorem source_query_eq (g : List Bool → List Bool) (p : List Bool) (t : ℕ) :
    (CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf
      (coefficientTask false) (coefficientTask true)).controller.query
      (((CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf
        (coefficientTask false) (coefficientTask true)).controller.reference g)^[t]
        (SingleCall.Program.initial p)) =
      if CannyResultantBits.RecursiveStage.selectRight a p then
        coefficientTask true (CannyResultantBits.RecursiveStage.rightQuery p)
      else coefficientTask false (CannyResultantBits.RecursiveStage.leftQuery a p) := by
  rw [CannyResultantBits.WithSquarefreeLeaves.program, SingleCall.Program.withLeaf_query_iterate]
  rfl

theorem request_source (q child : List Bool)
    (h : Requests (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf)
      (CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf (coefficientTask false) (coefficientTask true)).controller
      (fun _ => 1) q child) (hs : SelectedSource q) :
    isLeaf (pairFst (payload q)) = false ∧
    CannyResultantBits.RecursiveStage.request a (payload q) = true ∧
    child = if CannyResultantBits.RecursiveStage.selectRight a (payload q) then
      coefficientTask true (CannyResultantBits.RecursiveStage.rightQuery (payload q))
      else coefficientTask false (CannyResultantBits.RecursiveStage.leftQuery a (payload q)) := by
  obtain ⟨t, _, _, hn, he⟩ := h
  obtain ⟨hz, hd, hf, hm⟩ := hs
  rw [needs_iterate] at hn
  simp only [hz, hd, hf, hm, Bool.false_eq_true, ite_false] at hn
  change (CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf
    (coefficientTask false) (coefficientTask true)).controller.needs
    (((CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf
      (coefficientTask false) (coefficientTask true)).controller.reference
      (answer (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf)))^[t]
      (SingleCall.Program.initial (payload q))) = true at hn
  rw [CannyResultantBits.WithSquarefreeLeaves.program, SingleCall.Program.withLeaf_needs_iterate] at hn
  change (if isLeaf (pairFst (payload q)) then false
    else CannyResultantBits.RecursiveStage.request a (payload q)) = true at hn
  have hl : isLeaf (pairFst (payload q)) = false := by
    cases hh : isLeaf (pairFst (payload q)) <;> simp_all only [ite_true, ite_false, Bool.false_eq_true]
  refine ⟨hl, ?_, ?_⟩
  · simpa only [hl, Bool.false_eq_true, ite_false] using hn
  · rw [he, query_iterate]
    simp only [hz, hd, hf, hm, Bool.false_eq_true, ite_false]
    exact source_query_eq L a _ _ t

theorem request_measure_le (measure : List Bool → ℕ)
    (hz : ∀ c, measure [] ≤ measure c)
    (hc : ∀ right p, 0 < level (pairFst p) → measure (childInput right p) ≤ measure (pairFst p))
    (q child : List Bool)
    (h : Requests (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf)
      (CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf (coefficientTask false) (coefficientTask true)).controller
      (fun _ => 1) q child) : measure (origin child) ≤ measure (origin q) := by
  by_cases hs : SelectedSource q
  · obtain ⟨hl, _, he⟩ := request_source L a q child h hs
    have hh := (isLeaf_false_iff _).mp hl
    obtain ⟨hz, hd, hf, hm⟩ := hs
    have ho : origin q = pairFst (payload q) := by
      simp only [origin, hz, hd, hf, hm, Bool.false_eq_true, ite_false]
    rw [ho, he]
    split_ifs
    · change measure (childInput true (CannyResultantBits.RecursiveStage.rightQuery (payload q))) ≤ _
      have hp := CannyResultantBits.RecursiveStage.rightQuery_context (payload q)
      simpa only [hp] using hc true (CannyResultantBits.RecursiveStage.rightQuery (payload q)) (by rw [hp]; exact hh)
    · change measure (childInput false (CannyResultantBits.RecursiveStage.leftQuery a (payload q))) ≤ _
      have hp := CannyResultantBits.RecursiveStage.leftQuery_context a (payload q)
      simpa only [hp] using hc false (CannyResultantBits.RecursiveStage.leftQuery a (payload q)) (by rw [hp]; exact hh)
  · obtain ⟨t, _, _, hn, he⟩ := h
    rcases internal_query_origin _ _ _ q t hn hs with he0 | heo
    · rw [he, he0, origin_zero]
      exact hz _
    · rw [he, heo]

theorem reachable_measure_le (measure : List Bool → ℕ)
    (hz : ∀ c, measure [] ≤ measure c)
    (hc : ∀ right p, 0 < level (pairFst p) → measure (childInput right p) ≤ measure (pairFst p))
    (root q : List Bool) (hq : tasks L a root q) : measure (origin q) ≤ measure (origin root) := by
  change Relation.ReflTransGen _ root q at hq
  induction hq with
  | refl => exact le_refl _
  | @tail q child _ hstep ih => exact (request_measure_le L a measure hz hc q child hstep).trans ih

end LeanCanny.Algebra.CannyBalancedTaskRouting

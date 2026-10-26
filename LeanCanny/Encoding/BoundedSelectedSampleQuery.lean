/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSeparator

/-! # Single-sample formulas with both selected records charged in native space -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedSelectedSampleQuery
open LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open scoped Classical

theorem evaluator {P : Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (hp : (fun c => (p c).encode) ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℝ,
      BoundedCriticalSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c x ∧
        (p (pair c (BoundedCriticalSeparator.record P c))).Holds x)]) := by
  have hc := BoundedCriticalSampleQuery.selected_evaluator (h.comp pairFst_mem_FP) hp
    (fun q => ha (pairFst q))
  have E : SpaceFunction _ := ⟨hc.computable.comp (BoundedCriticalSeparator.evaluator h ha).withInput.computable⟩
  apply E.congr
  funext c
  apply congrArg List.singleton
  apply decide_eq_decide.mpr
  simp only [BoundedCriticalSampleQuery.Condition]
  simp only [BoundedFullDirectionChoice.record_comp]
  simp only [Readers.comp, Function.comp_apply, pairFst_pair]

theorem samples_evaluator {P : Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (hp : (fun c => (p c).encode) ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (∃ x : BoundedFullCriticalSamples.Samples P c,
      BoundedCriticalSampleQuery.Matches P c (p (pair c (BoundedCriticalSeparator.record P c))) x)]) := by
  apply (evaluator h hp ha).congr
  funext c
  rw [BoundedCriticalSampleQuery.selected_iff_samples]

end LeanCanny.Encoding.BoundedSelectedSampleQuery

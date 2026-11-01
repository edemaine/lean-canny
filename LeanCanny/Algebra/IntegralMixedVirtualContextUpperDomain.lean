/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextUpperModel
/-! # virtual upper arithmetic is zero outside its selected source context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextUpperDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualContextUpperBits
set_option backward.isDefEq.respectTransparency false

theorem model_invalid (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (q : List Bool) (hv : ¬ IntegralMixedVirtualCaps.valid P q) : (machine P a F h).model q = [] := by
  rw [machine_model]
  simp only [selectedFinite, selected, IntegralMixedVirtualContextBits.selected, hv, false_and,
    decide_false, Bool.false_and, Bool.cond_false]

theorem model_other_context (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (q : List Bool) (hx : ¬ IntegralMixedVirtualContextBits.context P q) : (machine P a F h).model q = [] := by
  rw [machine_model]
  simp only [selectedFinite, selected, IntegralMixedVirtualContextBits.selected, hx, and_false,
    decide_false, Bool.false_and, Bool.cond_false]
end LeanCanny.Algebra.IntegralMixedVirtualContextUpperDispatcherBits

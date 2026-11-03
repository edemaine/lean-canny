/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalPlanLookup
public import LeanCanny.Algebra.IntegralMixedFramedHistorySuccessor
/-! # The literal causal prefix grows by its decoded current-bank command

The record is instantiated against the already interpreted prefix, so its
current-denominator slope is exactly that prefix's Q. No future record or
root realization is used in this readback identity.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalPlanBits
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits
open scoped Classical

variable {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem prefix_successor (initial : State P S B 0 ι) (rs : List (Record n B))
    (h : rs.length≤S+1) (fallback : Instruction n B) (b : Fin rs.length) :
    paddedPast fallback (commands initial rs h) (b.val+1)=
      instantiate (run initial (paddedPast fallback (commands initial rs h) b.val)
        (by rw [paddedPast_length]; exact b.isLt.le.trans h)) rs.reverse[b.val] ::
        paddedPast fallback (commands initial rs h) b.val:=by
  rw [paddedPast_succ,chronological_instantiate initial rs h fallback b]
  rfl

theorem prefix_currentDenominator (initial : State P S B 0 ι) (rs : List (Record n B))
    (h : rs.length≤S+1) (fallback : Instruction n B) (b : Fin rs.length) :
    (chronological (commands initial rs h) b.val).getD fallback=
      instantiate (run initial (paddedPast fallback (commands initial rs h) b.val)
        (by rw [paddedPast_length]; exact b.isLt.le.trans h)) rs.reverse[b.val]:=by
  rw [chronological_instantiate initial rs h fallback b]
  rfl

end LeanCanny.Algebra.IntegralMixedCausalPlanBits

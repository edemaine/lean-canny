/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalScalarRecipe
/-! # Recipe identities for literal ordered, coarse and sweep constructors -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalScalarRecipe
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem expression_ordered {F : Inputs} (L : Layout F) (q : List Bool) (hm : L.mode q = 1)
    (r : Fin (arity F (L.input q))) (hr : r ∉ FlatAffineExceptionalOrderedRule.frozen F (L.input q)) :
    expression L q = (FlatAffineExceptionalOrderedRule.rule F L.height (L.input q) r hr).heights (L.row q) := by
  rw [expression, ite_eq_left hm]
  rfl

theorem expression_coarse {F : Inputs} (L : Layout F) (q : List Bool) (hm : L.mode q = 2) :
    expression L q = (FlatAffineExceptionalCoarseRule.rule F L.height (L.input q)).heights (L.row q) := by
  rw [expression, ite_eq_right (by omega), ite_eq_left hm]
  rfl

theorem expression_zero {F : Inputs} (L : Layout F) (q : List Bool) (h1 : L.mode q ≠ 1) (h2 : L.mode q ≠ 2) :
    expression L q = .constant 0 := by rw [expression, ite_eq_right h1, ite_eq_right h2]

theorem slope_sweep {F : Inputs} (L : Layout F) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (A : List Bool → ℕ) (q : List Bool) (hq : L.sweep q = true) (S : ℕ)
    (hb : FlatAffineExceptionalBankSource.births F (L.input q) ≤ S)
    (hf : L.height (L.input q) ∈ FlatAffineExceptionalOrderedRule.frozen F (L.input q))
    (r : Fin (arity F (L.input q))) (hr : r ∉ FlatAffineExceptionalOrderedRule.frozen F (L.input q)) :
    slope L C A q = if A q = (FlatAffineExceptionalOrderedRule.sweep F C L.height S (L.input q) hb hf r hr).height.val then
      (FlatAffineExceptionalOrderedRule.sweep F C L.height S (L.input q) hb hf r hr).slope else 0 := by
  rw [slope, hq, ite_eq_left rfl, FlatAffineExceptionalSlopeSource.slope_eq]
  rfl

theorem slope_default {F : Inputs} (L : Layout F) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (A : List Bool → ℕ) (q : List Bool) (hq : L.sweep q = false) :
    slope L C A q = if A q = 0 then 1 else 0 := by rw [slope, hq]; rfl
end LeanCanny.Encoding.FlatAffineExceptionalScalarRecipe

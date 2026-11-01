/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalMixedExpressions
public import LeanCanny.Algebra.IntegralMixedCoordinateRename
public import LeanCanny.Geometry.FrozenCoordinateOrdering
public import LeanCanny.Algebra.IntegralMixedCriticalSweep
/-! # The actual correlated bank admits a frozen-first mixed critical rule

Only spatial coordinate names are permuted. The actual coefficient prefix,
old physical tuple, parent/scalar labels and selected hom remain unchanged.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalOrderedRule
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births)
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def frozen (F : Inputs) (u : List Bool) := FlatAffineFullSourceTower.free F u (F.depth u)
noncomputable def order (F : Inputs) (u : List Bool) := FrozenCoordinateOrdering.permutation (frozen F u)

theorem ordered_frozen (F : Inputs) (u : List Bool) (i : Fin (arity F u)) :
    order F u i ∈ frozen F u ↔ i.val < (frozen F u).card := FrozenCoordinateOrdering.permutation_mem_iff _ _

theorem inverse_frozen (F : Inputs) (u : List Bool) (i : Fin (arity F u)) :
    ((order F u).symm i).val < (frozen F u).card ↔ i ∈ frozen F u := FrozenCoordinateOrdering.inverse_mem_iff _ _

noncomputable def state (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S+1) :=
  IntegralMixedCoordinateRename.state (FlatAffineExceptionalMixedHistory.initial F C h S u hm) (order F u)

noncomputable def rule (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool)
    (r : Fin (arity F u)) (hr : r ∉ frozen F u) : CriticalRule (F.source.dim u + 3) where
  offset := ⟨(frozen F u).card, FrozenCoordinateOrdering.card_lt _ r hr⟩
  objective := ((order F u).symm r).val - (frozen F u).card
  coordinate := 0
  scales _ := 2
  scales_ne_zero _ := by decide
  heights i := FlatAffineExceptionalMixedExpressions.shifted F h u (order F u i)

theorem rule_free (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S)
    (r : Fin (arity F u)) (hr : r ∉ frozen F u) :
    (data (state F C h S u (hm.trans (Nat.le_succ S))) hm (rule F h u r hr)).free = (order F u).symm r := by
  have H := ((order F u).symm r).isLt
  have HN : ¬ ((order F u).symm r).val < (frozen F u).card := fun hi => hr ((inverse_frozen F u r).mp hi)
  apply Fin.ext
  change (frozen F u).card + (((order F u).symm r).val - (frozen F u).card) %
    (F.source.dim u + 3 - (frozen F u).card + 1) = _
  rw [Nat.mod_eq_of_lt (by change ((order F u).symm r).val < F.source.dim u + 4 at H; omega)]
  omega

theorem rule_height (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S)
    (r : Fin (arity F u)) (hr : r ∉ frozen F u) (i : Fin (arity F u)) :
    (data (state F C h S u (hm.trans (Nat.le_succ S))) hm (rule F h u r hr)).heights i =
      FlatAffineExceptionalParentBank.shiftedNumerator F C h S u (hm.trans (Nat.le_succ S)) (order F u i) :=
  (IntegralMixedCoordinateRename.expression_eq _ _ _).trans
    (FlatAffineExceptionalMixedExpressions.shifted_eq F C h S u _ _)

theorem rule_scale (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S)
    (r : Fin (arity F u)) (hr : r ∉ frozen F u) (i : Fin (arity F u)) :
    (data (state F C h S u (hm.trans (Nat.le_succ S))) hm (rule F h u r hr)).scales i =
      2 * FlatAffineExceptionalParentBank.denominator F C h S u (hm.trans (Nat.le_succ S)) := by
  change _ * 2 = 2 * _
  exact mul_comm _ _

noncomputable def sweep (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S)
    (hh : h u ∈ frozen F u) (r : Fin (arity F u)) (hr : r ∉ frozen F u) : Rule (F.source.dim u+3) where
  critical := rule F h u r hr
  height := (order F u).symm (h u)
  height_frozen := (inverse_frozen F u (h u)).mpr hh
  slope := FlatAffineExceptionalParentBank.denominator F C h S u (hm.trans (Nat.le_succ S))
  slope_ne_zero := FlatAffineExceptionalParentBank.denominator_ne_zero F C h S u _

end LeanCanny.Encoding.FlatAffineExceptionalOrderedRule

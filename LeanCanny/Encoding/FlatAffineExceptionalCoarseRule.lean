/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalOrderedRule
/-! # The ordinary coarse-slice critical-height rule retains the same actual bank -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalCoarseRule
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births)
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def frozen (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) :=
  (FlatAffineExceptionalOrderedRule.frozen F u).erase (h u)
noncomputable def order (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) :=
  FrozenCoordinateOrdering.permutation (frozen F h u)
noncomputable def state (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S+1) :=
  IntegralMixedCoordinateRename.state (FlatAffineExceptionalMixedHistory.initial F C h S u hm) (order F h u)

noncomputable def rule (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) : CriticalRule (F.source.dim u+3) where
  offset := ⟨(frozen F h u).card, FrozenCoordinateOrdering.card_lt _ (h u) (Finset.notMem_erase _ _)⟩
  objective := ((order F h u).symm (h u)).val - (frozen F h u).card
  coordinate := ((order F h u).symm (h u)).val - (frozen F h u).card
  scales _ := 2
  scales_ne_zero _ := by decide
  heights i := FlatAffineExceptionalMixedExpressions.shifted F h u (order F h u i)

theorem local_height (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) :
    (frozen F h u).card ≤ ((order F h u).symm (h u)).val := by
  have H := FrozenCoordinateOrdering.inverse_mem_iff (frozen F h u) (h u)
  have HN : h u ∉ frozen F h u := Finset.notMem_erase _ _
  exact Nat.le_of_not_gt (fun HL => HN (H.mp HL))

theorem free_height (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S) :
    (data (state F C h S u (hm.trans (Nat.le_succ S))) hm (rule F h u)).free = (order F h u).symm (h u) := by
  have H := ((order F h u).symm (h u)).isLt
  have HL := local_height F h u
  apply Fin.ext
  change (frozen F h u).card + (((order F h u).symm (h u)).val - (frozen F h u).card) %
    (F.source.dim u + 3 - (frozen F h u).card + 1) = _
  rw [Nat.mod_eq_of_lt (by change ((order F h u).symm (h u)).val < F.source.dim u+4 at H; omega)]
  omega

theorem height_eq (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S) (i : Fin (arity F u)) :
    (data (state F C h S u (hm.trans (Nat.le_succ S))) hm (rule F h u)).heights i =
      FlatAffineExceptionalParentBank.shiftedNumerator F C h S u (hm.trans (Nat.le_succ S)) (order F h u i) :=
  (IntegralMixedCoordinateRename.expression_eq _ _ _).trans (FlatAffineExceptionalMixedExpressions.shifted_eq F C h S u _ _)

theorem scale_eq (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S) (i : Fin (arity F u)) :
    (data (state F C h S u (hm.trans (Nat.le_succ S))) hm (rule F h u)).scales i =
      2 * FlatAffineExceptionalParentBank.denominator F C h S u (hm.trans (Nat.le_succ S)) := by
  change _ * 2 = 2 * _
  exact mul_comm _ _

end LeanCanny.Encoding.FlatAffineExceptionalCoarseRule

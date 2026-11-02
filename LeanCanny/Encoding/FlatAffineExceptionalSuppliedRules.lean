/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedRecipe
/-! # Total ordered and coarse rule syntax from pinned supplied masks -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedRules
open LeanCanny.Algebra LeanCanny.Computation MatrixPower LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Source (F : Inputs) where
  input : List Bool → List Bool
  height : (u : List Bool) → Fin (arity F u)
  free : (u : List Bool) → Fin (arity F u)
  free_ne_height : ∀ u, free u ≠ height u
  mask : List Bool → List Bool
structure Access {F : Inputs} (S : Source F) : Prop where
  input : S.input ∈ FP
  height : BinaryFn (fun u => (S.height u).val)
  free : BinaryFn (fun u => (S.free u).val)
  mask : S.mask ∈ FP

noncomputable def frozen {F : Inputs} (S : Source F) (q : List Bool) :=
  SuppliedFrozenMaskBits.pinned (S.mask q) (S.height (S.input q)) (S.free (S.input q))
noncomputable def order {F : Inputs} (S : Source F) (q : List Bool) := FrozenCoordinateOrdering.permutation (frozen S q)
noncomputable def coarseFrozen {F : Inputs} (S : Source F) (q : List Bool) := (frozen S q).erase (S.height (S.input q))
noncomputable def coarseOrder {F : Inputs} (S : Source F) (q : List Bool) := FrozenCoordinateOrdering.permutation (coarseFrozen S q)

def maskWord {F : Inputs} (S : Source F) (q : List Bool) := SuppliedFrozenMaskBits.pinMask
  (arity F (S.input q)) (S.mask q) (S.height (S.input q)).val (S.free (S.input q)).val

theorem maskWord_FP {F : Inputs} (hF : F.Access) (S : Source F) (hS : Access S) : maskWord S ∈ FP :=
  SuppliedFrozenMaskBits.pinMask_FP _ ((FlatAffineFullSourceTower.arity_unary hF).comp hS.input) _ hS.mask
    _ _ (hS.height.comp hS.input) (hS.free.comp hS.input)

theorem maskWord_eq {F : Inputs} (S : Source F) (q : List Bool) : maskWord S q = FrozenCoordinatePermutationBits.mask (frozen S q) :=
  SuppliedFrozenMaskBits.pinMask_mask _ _ _

theorem height_mem {F : Inputs} (S : Source F) (q : List Bool) : S.height (S.input q) ∈ frozen S q :=
  SuppliedFrozenMaskBits.height_mem _ _ _
theorem free_not_mem {F : Inputs} (S : Source F) (q : List Bool) : S.free (S.input q) ∉ frozen S q :=
  SuppliedFrozenMaskBits.free_not_mem _ _ _ (S.free_ne_height _)

noncomputable def critical {F : Inputs} (S : Source F) (q : List Bool) : CriticalRule (F.source.dim (S.input q) + 3) where
  offset := ⟨(frozen S q).card, FrozenCoordinateOrdering.card_lt _ _ (free_not_mem S q)⟩
  objective := ((order S q).symm (S.free (S.input q))).val - (frozen S q).card
  coordinate := 0
  scales _ := 2
  scales_ne_zero _ := by decide
  heights i := FlatAffineExceptionalMixedExpressions.shifted F S.height (S.input q) (order S q i)

noncomputable def coarse {F : Inputs} (S : Source F) (q : List Bool) : CriticalRule (F.source.dim (S.input q) + 3) where
  offset := ⟨(coarseFrozen S q).card, FrozenCoordinateOrdering.card_lt _ _ (Finset.notMem_erase _ _)⟩
  objective := ((coarseOrder S q).symm (S.height (S.input q))).val - (coarseFrozen S q).card
  coordinate := ((coarseOrder S q).symm (S.height (S.input q))).val - (coarseFrozen S q).card
  scales _ := 2
  scales_ne_zero _ := by decide
  heights i := FlatAffineExceptionalMixedExpressions.shifted F S.height (S.input q) (coarseOrder S q i)

noncomputable def sweep {F : Inputs} (S : Source F) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (q : List Bool) : Rule (F.source.dim (S.input q) + 3) where
  critical := critical S q
  height := (order S q).symm (S.height (S.input q))
  height_frozen := (FrozenCoordinateOrdering.inverse_mem_iff _ _).mpr (height_mem S q)
  slope := FlatAffineExceptionalBankSource.denominator F C S.height (S.input q)
  slope_ne_zero := by
    rw [← FlatAffineExceptionalBankSource.denominator_bank F C S.height (FlatAffineExceptionalBankSource.births F (S.input q)) (S.input q) (Nat.le_succ _)]
    exact FlatAffineExceptionalParentBank.denominator_ne_zero _ _ _ _ _ _

theorem frozen_original {F : Inputs} (S : Source F) (q : List Bool)
    (hw : S.mask q = FrozenCoordinatePermutationBits.mask (FlatAffineExceptionalOrderedRule.frozen F (S.input q)))
    (hh : S.height (S.input q) ∈ FlatAffineExceptionalOrderedRule.frozen F (S.input q))
    (hr : S.free (S.input q) ∉ FlatAffineExceptionalOrderedRule.frozen F (S.input q)) :
    frozen S q = FlatAffineExceptionalOrderedRule.frozen F (S.input q) := by
  rw [frozen, hw, SuppliedFrozenMaskBits.pinned_original _ _ _ hh hr]

theorem critical_original {F : Inputs} (S : Source F) (q : List Bool)
    (hw : S.mask q = FrozenCoordinatePermutationBits.mask (FlatAffineExceptionalOrderedRule.frozen F (S.input q)))
    (hh : S.height (S.input q) ∈ FlatAffineExceptionalOrderedRule.frozen F (S.input q))
    (hr : S.free (S.input q) ∉ FlatAffineExceptionalOrderedRule.frozen F (S.input q)) :
    critical S q = FlatAffineExceptionalOrderedRule.rule F S.height (S.input q) (S.free (S.input q)) hr := by
  simp only [critical, order, frozen_original S q hw hh hr,
    FlatAffineExceptionalOrderedRule.rule, FlatAffineExceptionalOrderedRule.order]

theorem coarse_original {F : Inputs} (S : Source F) (q : List Bool)
    (hw : S.mask q = FrozenCoordinatePermutationBits.mask (FlatAffineExceptionalOrderedRule.frozen F (S.input q)))
    (hh : S.height (S.input q) ∈ FlatAffineExceptionalOrderedRule.frozen F (S.input q))
    (hr : S.free (S.input q) ∉ FlatAffineExceptionalOrderedRule.frozen F (S.input q)) :
    coarse S q = FlatAffineExceptionalCoarseRule.rule F S.height (S.input q) := by
  simp only [coarse, coarseOrder, coarseFrozen, frozen_original S q hw hh hr,
    FlatAffineExceptionalCoarseRule.rule, FlatAffineExceptionalCoarseRule.order, FlatAffineExceptionalCoarseRule.frozen]
end LeanCanny.Encoding.FlatAffineExceptionalSuppliedRules

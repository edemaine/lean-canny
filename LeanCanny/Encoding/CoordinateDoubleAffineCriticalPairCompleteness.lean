/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineMidpointPairRoots

/-! # Native labels for every pair of original critical roots

Every original pair is represented, and equal original parents make its
native shared-parent filter accept. Singular critical roots are included.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
open LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] memberRoot memberWord SquareSampleCompleteVertices.Valid

theorem exists_original_pair (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (x y : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u) :
    ∃ (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w),
      ∀ right : Bool, memberRoot P depth old level right u w hw = if right then y else x := by
  let e := FlatAffinePowerSampleInput.originalRootsEquiv
    (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u
  obtain ⟨w, hw, hm⟩ := exists_pair P depth old level u (e.symm x) (e.symm y)
  refine ⟨w, hw, ?_⟩
  intro right
  have H := congrArg e (hm right)
  unfold memberRoot
  cases right
  · exact H.trans (e.apply_symm_apply x)
  · exact H.trans (e.apply_symm_apply y)

theorem exists_shared_original_pair (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (x y : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u)
    (hshared : CoordinateDoubleAffineChildRecords.originalParent P depth old level u x =
      CoordinateDoubleAffineChildRecords.originalParent P depth old level u y) :
    ∃ (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w),
      LeanCanny.pair u w ∈ sharedLanguage P depth old level ∧
      memberRoot P depth old level false u w hw = x ∧ memberRoot P depth old level true u w hw = y := by
  obtain ⟨w, hw, hm⟩ := exists_original_pair P depth old level u x y
  have HL : memberRoot P depth old level false u w hw = x := hm false
  have HR : memberRoot P depth old level true u w hw = y := hm true
  refine ⟨w, hw, (shared_packet P depth old level u w hw).mpr ?_, HL, HR⟩
  change CoordinateDoubleAffineChildRecords.originalParent P depth old level u
      (memberRoot P depth old level false u w hw) =
    CoordinateDoubleAffineChildRecords.originalParent P depth old level u
      (memberRoot P depth old level true u w hw)
  rw [HL, HR]
  exact hshared

end LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs

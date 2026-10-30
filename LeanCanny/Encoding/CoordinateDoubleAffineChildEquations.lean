/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineChildGeometry

/-! # Fixed-height and exact midpoint equations of child slices -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
open LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] parent

noncomputable def retainedCoordinate (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (u : List Bool) (m : ℕ) (j : Fin m)
    (z : Fin (m * FlatAffineCriticalTower.width (P.dim u + 4)) → ℝ) : ℝ :=
  z (TriangularPolynomialRows.block (FlatAffineCriticalTower.width (P.dim u + 4)) j.val m j.isLt
    (FlatAffineCriticalTower.blockEquiv (P.dim u + 4) (Sum.inl (coordinateFin P depth old u))))

theorem ancestralCoordinate (n m : ℕ) (j : Fin m) (i : Fin n) (z : Fin (m * FlatAffineCriticalTower.width n) → ℝ) :
    (z ∘ TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width n) m)
        (FlatAffineCriticalTower.oldAmbient m j i) =
      z (TriangularPolynomialRows.block (FlatAffineCriticalTower.width n) j.val m j.isLt
        (FlatAffineCriticalTower.blockEquiv n (Sum.inl i))) := by
  apply congrArg z
  apply Fin.ext
  exact FlatAffineCriticalTower.oldAmbient_index m j i

theorem newValue_height (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ) (u : List Bool)
    (z : Fin ((depth u + 1) * FlatAffineCriticalTower.width (P.dim u + 4)) → ℝ) :
    newValue false P depth old u z =
      2 * retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩ z := by
  have H := CoordinateHeightRecord.eval_height (coordinateFin P depth old u) (⟨depth u, by omega⟩ : Fin (depth u + 1))
    (z ∘ TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (P.dim u + 4)) (depth u + 1))
  exact H.trans (congrArg (fun v : ℝ => 2 * v)
    (ancestralCoordinate (P.dim u + 4) (depth u + 1) ⟨depth u, by omega⟩ (coordinateFin P depth old u) z))

theorem newValue_midpoint (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ) (u : List Bool)
    (z : Fin ((depth u + 2) * FlatAffineCriticalTower.width (P.dim u + 4)) → ℝ) :
    newValue true P depth old u z =
      retainedCoordinate P depth old u (depth u + 2) ⟨depth u, by omega⟩ z +
        retainedCoordinate P depth old u (depth u + 2) ⟨depth u + 1, by omega⟩ z := by
  have H := CoordinateHeightRecord.eval_midpoint (coordinateFin P depth old u)
    (⟨depth u, by omega⟩ : Fin (depth u + 2)) (⟨depth u + 1, by omega⟩ : Fin (depth u + 2))
    (z ∘ TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (P.dim u + 4)) (depth u + 2))
  exact H.trans (congrArg₂ (fun a b : ℝ => a + b)
    (ancestralCoordinate (P.dim u + 4) (depth u + 2) ⟨depth u, by omega⟩ (coordinateFin P depth old u) z)
    (ancestralCoordinate (P.dim u + 4) (depth u + 2) ⟨depth u + 1, by omega⟩ (coordinateFin P depth old u) z))

theorem doubled_slice {α : Type*} (S : Set α) (f : α → ℝ) (v : ℝ) :
    {y | y ∈ S ∧ 2 * f y = 2 * v} = {y | y ∈ S ∧ f y = v} := by
  ext y
  exact and_congr Iff.rfl ⟨mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), congrArg (fun v : ℝ => 2 * v)⟩

theorem slice_height (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (hn : old (FlatAffineFullSourceTower.stage u (depth u)) < P.dim u + 3)
    (z : FlatAffinePowerSampleInput.OriginalRoots (inputs false P depth old level) u) :
    FlatAffineCompleteComponentSamples.slice (inputs false P depth old level) u z =
      {y | y ∈ FlatAffineCompleteComponentSamples.slice (CoordinateDoubleAffinePrefix.inputs P depth old level) u
        (parent false P depth old level u z) ∧ y (coordinateFin P depth old u) =
          retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩ z.val} :=
  (slice_eq false P depth old level u hn z).trans
    ((congrArg (fun v => {y | y ∈ FlatAffineCompleteComponentSamples.slice
        (CoordinateDoubleAffinePrefix.inputs P depth old level) u (parent false P depth old level u z) ∧
          2 * y (coordinateFin P depth old u) = v}) (newValue_height P depth old u z.val)).trans
      (doubled_slice _ _ _))

theorem slice_midpoint (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (hn : old (FlatAffineFullSourceTower.stage u (depth u)) < P.dim u + 3)
    (z : FlatAffinePowerSampleInput.OriginalRoots (inputs true P depth old level) u) :
    FlatAffineCompleteComponentSamples.slice (inputs true P depth old level) u z =
      {y | y ∈ FlatAffineCompleteComponentSamples.slice (CoordinateDoubleAffinePrefix.inputs P depth old level) u
        (parent true P depth old level u z) ∧ 2 * y (coordinateFin P depth old u) =
          retainedCoordinate P depth old u (depth u + 2) ⟨depth u, by omega⟩ z.val +
            retainedCoordinate P depth old u (depth u + 2) ⟨depth u + 1, by omega⟩ z.val} :=
  (slice_eq true P depth old level u hn z).trans
    (congrArg (fun v => {y | y ∈ FlatAffineCompleteComponentSamples.slice
      (CoordinateDoubleAffinePrefix.inputs P depth old level) u (parent true P depth old level u z) ∧
        2 * y (coordinateFin P depth old u) = v}) (newValue_midpoint P depth old u z.val))

end LeanCanny.Encoding.CoordinateDoubleAffineChildRecords

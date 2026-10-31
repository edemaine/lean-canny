/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineChildRetainedStages

/-! # The first retained critical sample in a midpoint child

The first new critical block of a midpoint child is the original next-stage
system. Its first critical root is retained without duplicating its ancestry.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
open LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

noncomputable def midpointPrefix (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : FlatAffineFullSourceTower.Inputs :=
  FlatAffineCompleteRootStages.truncate (inputs true P depth old level) (fun u => depth u + 1)

theorem midpoint_first_row (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) :
    (FlatAffineFullSourceTower.family (inputs true P depth old level) u).row (depth u) =
      (FlatAffineFullSourceTower.family (CoordinateDoubleAffinePrefix.inputs P depth old level) u).row (depth u) := by
  have hh : depth u < childDepth true depth u := by change depth u < depth u + 2; omega
  have HF := free_retained true P depth old level u (depth u) (le_refl _) hh
  have HD := direction_retained true P depth old level u (depth u) (le_refl _) hh
  have HL := funext (fun j : Fin (P.dim u + 4) =>
    (level_retained true P depth old level u (depth u) (le_refl _) hh j).trans
      (FlatAffineCriticalTower.Level.extend_refl _))
  let build (s : Finset (Fin (P.dim u + 4))) (a : Fin (P.dim u + 4 + 1) → Fin (P.dim u + 4) → ℤ)
      (b : Fin (P.dim u + 4) → FlatAffineCriticalTower.Level (P.dim u + 4) (depth u) ℤ) :=
    fun i : Fin (FlatAffineCriticalTower.width (P.dim u + 4)) =>
      MvPolynomial.rename
        (Equiv.sumCongr (Equiv.refl (FlatAffineCriticalTower.Ancestors (P.dim u + 4) (depth u)))
          (FlatAffineCriticalTower.blockEquiv (P.dim u + 4)))
        (FlatAffineCriticalStage.row (BoundedFullCriticalSamples.polynomial P u) s a
          (fun j => (b j).polynomial) ((FlatAffineCriticalTower.blockEquiv (P.dim u + 4)).symm i))
  change build (FlatAffineFullSourceTower.free (inputs true P depth old level) u (depth u))
      (FlatAffineFullSourceTower.direction (inputs true P depth old level) u (depth u))
      (FlatAffineFullSourceTower.level (inputs true P depth old level) u (depth u)) =
    build (FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u))
      (FlatAffineFullSourceTower.direction (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u))
      (FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u))
  rw [HF, HD, HL]

theorem midpoint_prefix_system (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) :
    FlatAffineFullSourceTower.system (midpointPrefix P depth old level) u =
      FlatAffineFullSourceTower.system
        (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u := by
  apply TriangularPolynomialIndexing.system_congr _ _ (depth u + 1)
  intro j hj
  by_cases h : j < depth u
  · exact family_row_before true P depth old level u j h
  · have he : j = depth u := by omega
    subst j
    exact midpoint_first_row P depth old level u

noncomputable def midpointPrefixRoot (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u) :
    FlatAffinePowerSampleInput.OriginalRoots (midpointPrefix P depth old level) u :=
  ⟨z.val, fun i =>
    (congrArg (fun f => (f i).eval₂ (Int.castRingHom ℝ) z.val)
      (midpoint_prefix_system P depth old level u)).trans (z.property i)⟩

attribute [local irreducible] midpointPrefixRoot

theorem midpointPrefixRoot_val (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u) :
    (midpointPrefixRoot P depth old level u z).val = z.val := by
  unfold midpointPrefixRoot
  rfl

end LeanCanny.Encoding.CoordinateDoubleAffineChildRecords

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineMidpointPrefix
public import LeanCanny.Encoding.CoordinateDoubleAffineChildGeometry
public import LeanCanny.Encoding.FlatAffineCompleteChildGeometry
public import LeanCanny.Algebra.FlatAffineCriticalStageRootTransport

/-! # Constructing a midpoint child from two compatible critical roots

The left sample supplies the shared ancestry and first critical block. The
right sample supplies only its newest block. Equality of their original
parents transports the copied affine levels, including at singular roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
open LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] midpointPrefixRoot BoundedFullCriticalSamples.polynomial

noncomputable def originalParent (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u) :
    FlatAffinePowerSampleInput.OriginalRoots (CoordinateDoubleAffinePrefix.inputs P depth old level) u :=
  FlatAffineCompleteRootStages.project
    (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) depth u
    (by change depth u ≤ depth u + 1; omega) z

theorem originalParent_val (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u) :
    (originalParent P depth old level u z).val = z.val ∘
      TriangularPolynomialRows.prefixIndex (FlatAffineCriticalTower.width (P.dim u + 4))
        (depth u) (depth u + 1) (by omega) :=
  project_val (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) depth u
    (by change depth u ≤ depth u + 1; omega) z

attribute [local irreducible] originalParent

theorem midpoint_prefix_parent_val (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u) :
    (originalParent P depth old level u z).val = (midpointPrefixRoot P depth old level u z).val ∘
      TriangularPolynomialRows.prefixIndex (FlatAffineCriticalTower.width (P.dim u + 4))
        (depth u) (depth u + 1) (by omega) := by
  have H := congrArg (fun x : Fin ((depth u + 1) * FlatAffineCriticalTower.width (P.dim u + 4)) → ℝ =>
    x ∘ TriangularPolynomialRows.prefixIndex (FlatAffineCriticalTower.width (P.dim u + 4))
      (depth u) (depth u + 1) (by omega)) (midpointPrefixRoot_val P depth old level u z)
  exact (originalParent_val P depth old level u z).trans H.symm

theorem midpoint_level_value (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u)
    (j : Fin (P.dim u + 4)) :
    (FlatAffineFullSourceTower.level (inputs true P depth old level) u (depth u + 1) j).polynomial.eval₂
        (Int.castRingHom ℝ) ((midpointPrefixRoot P depth old level u z).val ∘
          TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (P.dim u + 4)) (depth u + 1)) =
      (FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u) j).polynomial.eval₂
        (Int.castRingHom ℝ) ((originalParent P depth old level u z).val ∘
          TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (P.dim u + 4)) (depth u)) := by
  have hd : depth u ≤ depth u + 1 := by omega
  have hh : depth u + 1 < childDepth true depth u := by change depth u + 1 < depth u + 2; omega
  have HL := level_retained true P depth old level u (depth u + 1) hd hh j
  have HE := congrArg (fun b : FlatAffineCriticalTower.Level (P.dim u + 4) (depth u + 1) ℤ =>
    b.polynomial.eval₂ (Int.castRingHom ℝ) ((midpointPrefixRoot P depth old level u z).val ∘
      TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (P.dim u + 4)) (depth u + 1))) HL
  have HX := congrArg (fun x : Fin (depth u * FlatAffineCriticalTower.width (P.dim u + 4)) → ℝ =>
    (FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u) j).polynomial.eval₂
      (Int.castRingHom ℝ) (x ∘ TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (P.dim u + 4)) (depth u)))
    (midpoint_prefix_parent_val P depth old level u z)
  exact HE.trans ((FlatAffineCriticalTower.Level.eval_extend_prefix (Int.castRingHom ℝ) hd
    (FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u) j)
      (midpointPrefixRoot P depth old level u z).val).trans HX.symm)

theorem midpoint_right_stage (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (left right : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u)
    (hshared : originalParent P depth old level u left = originalParent P depth old level u right) :
    ∀ i, (FlatAffineCriticalStage.row (BoundedFullCriticalSamples.polynomial P u)
      (FlatAffineFullSourceTower.free (inputs true P depth old level) u (depth u + 1))
      (FlatAffineFullSourceTower.direction (inputs true P depth old level) u (depth u + 1))
      (fun j => (FlatAffineFullSourceTower.level (inputs true P depth old level) u (depth u + 1) j).polynomial) i).eval₂
        (Int.castRingHom ℝ)
        (Sum.elim ((midpointPrefixRoot P depth old level u left).val ∘
          TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (P.dim u + 4)) (depth u + 1))
          (FlatAffineCompleteRootStages.newest (CoordinateDoubleAffinePrefix.inputs P depth old level) u right.val)) = 0 := by
  let F := CoordinateDoubleAffinePrefix.inputs P depth old level
  have hd : depth u ≤ depth u + 1 := by omega
  have hh : depth u + 1 < childDepth true depth u := by change depth u + 1 < depth u + 2; omega
  have HF := free_retained true P depth old level u (depth u + 1) hd hh
  have HD := direction_retained true P depth old level u (depth u + 1) hd hh
  have HB (j : Fin (P.dim u + 4)) := congrArg (fun x : FlatAffinePowerSampleInput.OriginalRoots F u =>
    (FlatAffineFullSourceTower.level F u (depth u) j).polynomial.eval₂ (Int.castRingHom ℝ)
      (x.val ∘ TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (P.dim u + 4)) (depth u))) hshared
  have HR : ∀ i, (FlatAffineCriticalStage.row (BoundedFullCriticalSamples.polynomial P u)
      (FlatAffineFullSourceTower.free F u (depth u)) (FlatAffineFullSourceTower.direction F u (depth u))
      (fun j => (FlatAffineFullSourceTower.level F u (depth u) j).polynomial) i).eval₂ (Int.castRingHom ℝ)
        (Sum.elim ((originalParent P depth old level u right).val ∘
          TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (P.dim u + 4)) (depth u))
          (FlatAffineCompleteRootStages.newest F u right.val)) = 0 := by
    unfold originalParent
    exact FlatAffineCompleteChildGeometry.newest_roots F u right
  exact (FlatAffineCriticalStage.roots_congr_point (Int.castRingHom ℝ) (BoundedFullCriticalSamples.polynomial P u)
    (FlatAffineFullSourceTower.free F u (depth u)) (FlatAffineFullSourceTower.free (inputs true P depth old level) u (depth u + 1))
    (FlatAffineFullSourceTower.direction F u (depth u)) (FlatAffineFullSourceTower.direction (inputs true P depth old level) u (depth u + 1))
    (fun j => (FlatAffineFullSourceTower.level F u (depth u) j).polynomial)
    (fun j => (FlatAffineFullSourceTower.level (inputs true P depth old level) u (depth u + 1) j).polynomial)
    ((originalParent P depth old level u right).val ∘ TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (P.dim u + 4)) (depth u))
    ((midpointPrefixRoot P depth old level u left).val ∘ TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (P.dim u + 4)) (depth u + 1))
    (FlatAffineCompleteRootStages.newest F u right.val) HF.symm HD.symm
    (fun j => ((midpoint_level_value P depth old level u left j).trans (HB j)).symm)).mp
      HR

noncomputable def midpointRoot (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (left right : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u)
    (hshared : originalParent P depth old level u left = originalParent P depth old level u right) :
    FlatAffinePowerSampleInput.OriginalRoots (inputs true P depth old level) u :=
  FlatAffineCompleteRootStages.extend (midpointPrefix P depth old level) u (midpointPrefixRoot P depth old level u left)
    (FlatAffineCompleteRootStages.newest (CoordinateDoubleAffinePrefix.inputs P depth old level) u right.val)
    (midpoint_right_stage P depth old level u left right hshared)

end LeanCanny.Encoding.CoordinateDoubleAffineChildRecords

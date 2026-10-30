/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerPrefix

/-! # Computed ancestry in the original affine Lagrange tower

Removing the zero coordinate and undoing multiplier powers commute with
prefix projection. The native power-root label therefore names precisely
the original ancestor, including singular ancestors and descendants.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineAncestorLabels
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineCompleteRootStages (truncate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

lemma original_projection (F : Inputs) (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u : List Bool)
    (z : {z : Fin (FlatAffineFullSourcePositive.count F u) → ℝ //
      ∀ i, (FlatAffinePowerPositive.system F u i).eval₂ (Int.castRingHom ℝ) z = 0}) :
    FlatAffinePowerSampleInput.originalRootsEquiv (truncate F d) u
      ⟨z.val ∘ FlatAffinePowerPrefix.projection F d hd u,
        FlatAffinePowerPrefix.roots_prefix (Int.castRingHom ℝ) F d hd u z.val z.property⟩ =
    FlatAffineCompleteRootStages.project F d u (hd u) (FlatAffinePowerSampleInput.originalRootsEquiv F u z) := by
  apply Subtype.ext
  funext i
  change FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree (truncate F d) u)
    ((z.val ∘ FlatAffinePowerPrefix.projection F d hd u) ∘ Fin.castSucc) i =
    FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree F u) (z.val ∘ Fin.castSucc)
      (FlatAffineCompleteRootStages.prefixIndex F d u (hd u) i)
  have HE : ((z.val ∘ FlatAffinePowerPrefix.projection F d hd u) ∘ Fin.castSucc) =
      (z.val ∘ Fin.castSucc) ∘ FlatAffinePowerTower.prefixIndex (hd u) := by
    funext j
    simp only [Function.comp_apply, FlatAffinePowerPrefix.projection_old]
  change FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree F u)
    ((z.val ∘ FlatAffinePowerPrefix.projection F d hd u) ∘ Fin.castSucc) i =
    (FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree F u) (z.val ∘ Fin.castSucc) ∘
      FlatAffinePowerTower.prefixIndex (hd u)) i
  rw [HE]
  exact congrFun (FlatAffinePowerTower.powerPoint_prefix (hd u) (FlatAffinePowerControls.degree F u)
    (z.val ∘ Fin.castSucc)) i

theorem value_original (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u w : List Bool)
    (hw : FlatAffineCompleteVertices.Valid F cone u w) :
    FlatAffineCompleteVertices.vertexEquiv (truncate F d) (FlatAffineCompleteRootStages.cone_prefix F cone d hd) u
      ⟨FlatAffinePowerPrefix.value F cone d hd (pair u w), FlatAffinePowerPrefix.value_valid F cone d hd u w hw⟩ =
    FlatAffineCompleteRootStages.project F d u (hd u) (FlatAffineCompleteVertices.vertexEquiv F cone u ⟨w, hw⟩) := by
  have H := FlatAffinePowerPrefix.value_point F cone d hd u w hw
  have HE : SquareSampleCompleteVertices.candidate
      (FlatAffinePowerSampleInput.input (truncate F d) (FlatAffineCompleteRootStages.cone_prefix F cone d hd))
      u (FlatAffinePowerPrefix.value F cone d hd (pair u w)) (FlatAffinePowerPrefix.value_valid F cone d hd u w hw) =
    ⟨(SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F cone) u w hw).val ∘
        FlatAffinePowerPrefix.projection F d hd u,
      FlatAffinePowerPrefix.roots_prefix (Int.castRingHom ℝ) F d hd u _
        (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F cone) u w hw).property⟩ := Subtype.ext H
  change FlatAffinePowerSampleInput.originalRootsEquiv (truncate F d) u
    (SquareSampleCompleteVertices.candidate
      (FlatAffinePowerSampleInput.input (truncate F d) (FlatAffineCompleteRootStages.cone_prefix F cone d hd))
      u (FlatAffinePowerPrefix.value F cone d hd (pair u w)) (FlatAffinePowerPrefix.value_valid F cone d hd u w hw)) = _
  rw [HE, original_projection]
  rfl

end LeanCanny.Encoding.FlatAffineAncestorLabels

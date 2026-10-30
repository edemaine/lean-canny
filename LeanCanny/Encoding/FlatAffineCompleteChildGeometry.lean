/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSingularChildLabels

/-! # Feasibility and singularity of accepted complete children

Every next-stage root satisfies the frozen equations over its exact prefix.
A zero objective multiplier forces a singular slice point. Consequently the
native singular-child selector is sound as well as complete, without any
Jacobian premise on the larger critical system.
-/

@[expose] public section
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next newest project)
open FlatAffineCompleteComponentSamples (source active direction levels ancestors slice)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
namespace LeanCanny.Encoding.FlatAffineCompleteChildGeometry

lemma stagePoint_eq (F : Inputs) (u : List Bool) (r : FlatAffinePowerSampleInput.OriginalRoots (next F) u) :
    FlatAffineTowerRegularity.stagePoint (F.depth u) (F.depth u + 1) (by omega) r.val =
      Sum.elim (ancestors F u (project (next F) F.depth u (FlatAffineCompleteChildLabels.depth_le F u) r).val)
        (newest F u r.val) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => rfl

theorem newest_roots (F : Inputs) (u : List Bool) (r : FlatAffinePowerSampleInput.OriginalRoots (next F) u) :
    ∀ i, (FlatAffineCriticalStage.row (source F u) (active F u) (direction F u) (levels F u) i).eval₂ (Int.castRingHom ℝ)
      (Sum.elim (ancestors F u (project (next F) F.depth u (FlatAffineCompleteChildLabels.depth_le F u) r).val)
        (newest F u r.val)) = 0 := by
  have H := (FlatAffineTowerRegularity.roots_iff_stages (Int.castRingHom ℝ) (source F u)
    (FlatAffineFullSourceTower.free F u) (FlatAffineFullSourceTower.direction F u) (FlatAffineFullSourceTower.level F u)
    (F.depth u + 1) r.val).mp r.property (F.depth u) (Nat.lt_succ_self _)
  rw [stagePoint_eq] at H
  exact H

theorem newest_slice (F : Inputs) (u : List Bool) (r : FlatAffinePowerSampleInput.OriginalRoots (next F) u) :
    newest F u r.val ∘ Sum.inl ∈ slice F u (project (next F) F.depth u (FlatAffineCompleteChildLabels.depth_le F u) r) := by
  have H := (FlatAffineCriticalStage.roots_iff (Int.castRingHom ℝ) (source F u) (active F u)
    (direction F u) (levels F u) _).mp (newest_roots F u r)
  exact ⟨H.1, H.2.1⟩

theorem newest_singular (F : Inputs) (u : List Bool) (r : FlatAffinePowerSampleInput.OriginalRoots (next F) u)
    (hmu : newest F u r.val (Sum.inr 0) = 0) :
    newest F u r.val ∘ Sum.inl ∈ FlatAffineSingularSliceSamples.singular F u
      (project (next F) F.depth u (FlatAffineCompleteChildLabels.depth_le F u) r) := by
  refine ⟨newest_slice F u r, ?_⟩
  have H := newest_roots F u r
  have HE : newest F u r.val = Sum.elim (newest F u r.val ∘ Sum.inl) (newest F u r.val ∘ Sum.inr) := by
    funext j
    cases j <;> rfl
  rw [HE] at H
  exact FlatAffineSingularCriticalRoot.singular_of_zero_multiplier (Int.castRingHom ℝ)
    (source F u) (active F u) (direction F u) (levels F u)
    (ancestors F u (project (next F) F.depth u (FlatAffineCompleteChildLabels.depth_le F u) r).val)
    (newest F u r.val ∘ Sum.inl) (newest F u r.val ∘ Sum.inr) H hmu

theorem singular_sound (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u w v : List Bool) (hw : FlatAffineCompleteVertices.Valid (next F) cone u w)
    (hv : FlatAffineCompleteVertices.Valid F (FlatAffineCompleteChildLabels.parentCone F cone) u v)
    (h : pair u (pair w v) ∈ FlatAffineSingularChildLabels.language F cone) :
    newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨w, hw⟩).val ∘ Sum.inl ∈
      FlatAffineSingularSliceSamples.singular F u
        (FlatAffineCompleteVertices.vertexEquiv F (FlatAffineCompleteChildLabels.parentCone F cone) u ⟨v, hv⟩) := by
  have H := (FlatAffineSingularChildLabels.packet F cone u w v hw).mp h
  have HP := (FlatAffineCompleteChildLabels.packet F cone u w v hw hv).mp H.1
  have HS := newest_singular F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨w, hw⟩) H.2
  rwa [HP] at HS
end LeanCanny.Encoding.FlatAffineCompleteChildGeometry

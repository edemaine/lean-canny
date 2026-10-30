/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineCompleteChildLabels
public import LeanCanny.Encoding.FlatAffineSingularSliceSamples

/-! # Ancestry-checked component samples and singular slice points

Complete critical labels are accepted by the actual native child selector.
Compact regular slices have a joined accepted sample in every component;
every singular slice point has an accepted label over its exact parent when
the slice normals are independent.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineCompleteChildSamples
open Set LeanCanny.Algebra LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next newest)
open FlatAffineCompleteComponentSamples (source active direction slice)
open FlatAffineCompleteChildLabels (parentCone language)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem exists_joined_accepted (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v)
    (hcompact : IsCompact (slice F u (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩)))
    (hregular : ∀ y ∈ slice F u (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩), Function.Surjective
      (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ) (source F u) (active F u) (direction F u) y))
    (hindependent : ¬∃ c : active F u → ℝ, ∀ i,
      (direction F u 0 i : ℝ) = ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ))
    (z : Fin (arity F u) → ℝ)
    (hz : z ∈ slice F u (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩)) :
    ∃ w : {w : List Bool // FlatAffineCompleteVertices.Valid (next F) cone u w},
      pair u (pair w.val v) ∈ language F cone ∧
      JoinedIn (slice F u (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩)) z
        (newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u w).val ∘ Sum.inl) := by
  obtain ⟨w, hj, hp⟩ := FlatAffineCompleteComponentSamples.exists_joined_label F cone u
    (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩)
    hcompact hregular hindependent z hz
  exact ⟨w, (FlatAffineCompleteChildLabels.packet F cone u w.val v w.property hv).mpr hp, hj⟩

theorem singular_accepted (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v)
    (hheights : ∀ c : active F u → ℝ, (∀ i, ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ) = 0) → ∀ j, c j = 0)
    (z : Fin (arity F u) → ℝ)
    (hz : z ∈ FlatAffineSingularSliceSamples.singular F u
      (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩)) :
    ∃ w : {w : List Bool // FlatAffineCompleteVertices.Valid (next F) cone u w},
      pair u (pair w.val v) ∈ language F cone ∧
      newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u w).val ∘ Sum.inl = z ∧
      newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u w).val (Sum.inr 0) = 0 := by
  obtain ⟨w, hp, hz, hmu⟩ := FlatAffineSingularSliceSamples.exists_label F cone u
    (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩) hheights z hz
  exact ⟨w, (FlatAffineCompleteChildLabels.packet F cone u w.val v w.property hv).mpr hp, hz, hmu⟩

end LeanCanny.Encoding.FlatAffineCompleteChildSamples

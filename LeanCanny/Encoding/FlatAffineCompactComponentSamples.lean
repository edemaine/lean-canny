/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineSingularComponentSampling
public import LeanCanny.Geometry.ComponentFiniteSamples
public import LeanCanny.Encoding.FlatAffineCompleteChildLabels
public import LeanCanny.Encoding.FlatAffineCompleteComponentSamples

/-! # Native complete samples in compact slice components

Independent affine normals suffice to sample every connected component,
including singular components. Each sample passes the actual native child
test with the original parent's complete label. Global regularity of the
slice and regularity of the critical system are unnecessary.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineCompactComponentSamples
open Set LeanCanny.Algebra LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next newest)
open FlatAffineCompleteComponentSamples (source active direction levels ancestors slice)
open FlatAffineCompleteChildLabels (parentCone language)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem exists_accepted (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v)
    (hcompact : IsCompact (slice F u (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩)))
    (hheights : ∀ c : active F u → ℝ, (∀ i, ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ) = 0) → ∀ j, c j = 0)
    (hindependent : ¬∃ c : active F u → ℝ, ∀ i,
      (direction F u 0 i : ℝ) = ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ))
    (z : Fin (arity F u) → ℝ)
    (hz : z ∈ slice F u (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩)) :
    ∃ w : {w : List Bool // FlatAffineCompleteVertices.Valid (next F) cone u w},
      pair u (pair w.val v) ∈ language F cone ∧
      newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u w).val ∘ Sum.inl ∈
        connectedComponentIn (slice F u (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩)) z := by
  let x := FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩
  obtain ⟨y, mu, hc, hroot⟩ := FlatAffineSingularComponentSampling.exists_component_stage_root (Int.castRingHom ℝ)
    (source F u) (active F u) (direction F u) (levels F u) (ancestors F u x.val)
    hcompact hheights hindependent z hz.1 hz.2
  let root := FlatAffineCompleteRootStages.extend F u x (Sum.elim y mu) hroot
  let w := (FlatAffineCompleteVertices.vertexEquiv (next F) cone u).symm root
  have HW : FlatAffineCompleteVertices.vertexEquiv (next F) cone u w = root := Equiv.apply_symm_apply _ _
  refine ⟨w, ?_, ?_⟩
  · apply (FlatAffineCompleteChildLabels.packet F cone u w.val v w.property hv).mpr
    rw [HW]
    exact FlatAffineCompleteRootStages.extend_prefix F u x (Sum.elim y mu) hroot
  · rw [HW, FlatAffineCompleteRootStages.extend_newest]
    exact hc

theorem exists_root (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (hcompact : IsCompact (slice F u x))
    (hheights : ∀ c : active F u → ℝ, (∀ i, ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ) = 0) → ∀ j, c j = 0)
    (hindependent : ¬∃ c : active F u → ℝ, ∀ i,
      (direction F u 0 i : ℝ) = ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ))
    (z : Fin (arity F u) → ℝ) (hz : z ∈ slice F u x) :
    ∃ r : FlatAffinePowerSampleInput.OriginalRoots (next F) u,
      newest F u r.val ∘ Sum.inl ∈ connectedComponentIn (slice F u x) z := by
  let v := (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u).symm x
  have HV : FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u v = x := Equiv.apply_symm_apply _ _
  obtain ⟨w, _, hc⟩ := exists_accepted F cone u v.val v.property
    (by simpa only [HV] using hcompact) hheights hindependent z (by simpa only [HV] using hz)
  exact ⟨FlatAffineCompleteVertices.vertexEquiv (next F) cone u w, by simpa only [HV] using hc⟩

theorem finite_card_le (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (hcompact : IsCompact (slice F u x))
    (hheights : ∀ c : active F u → ℝ, (∀ i, ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ) = 0) → ∀ j, c j = 0)
    (hindependent : ¬∃ c : active F u → ℝ, ∀ i,
      (direction F u 0 i : ℝ) = ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ)) :
    Finite (ConnectedComponents (slice F u x)) ∧
      Nat.card (ConnectedComponents (slice F u x)) ≤ FlatAffinePowerSampleInput.originalCountBound (next F) u := by
  let I := FlatAffinePowerSampleInput.input (next F) cone
  let : Finite (SquareSampleComplete.Roots I u) :=
    (SquareSampleComplete.finite_roots I (FlatAffinePowerSampleInput.complete (next F) cone) u).1
  let : Finite (FlatAffinePowerSampleInput.OriginalRoots (next F) u) :=
    Finite.of_equiv (SquareSampleComplete.Roots I u) (FlatAffinePowerSampleInput.originalRootsEquiv (next F) u)
  have H := ComponentFiniteSamples.finite_card_le (slice F u x)
    (fun r : FlatAffinePowerSampleInput.OriginalRoots (next F) u => newest F u r.val ∘ Sum.inl)
    (fun z hz => exists_root F cone u x hcompact hheights hindependent z hz)
  exact ⟨H.1, H.2.trans (FlatAffinePowerSampleInput.originalCount_le (next F) cone u)⟩

end LeanCanny.Encoding.FlatAffineCompactComponentSamples

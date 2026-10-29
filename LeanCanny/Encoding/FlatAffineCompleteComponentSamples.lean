/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineCompleteRootStages
public import LeanCanny.Geometry.FlatAffineComponentSampling

/-! # Complete critical labels sample compact regular affine slices

Any original parent root can be extended by a component sample. Complete
labels retain the resulting critical root even when the parent or the full
critical stage is singular. Slice regularity still supplies the joined
maximum used here; singular slice components need a separate argument.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineCompleteComponentSamples
open LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity count stageWidth)
open FlatAffineCompleteRootStages (next newest)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def source (F : Inputs) (u : List Bool) := BoundedFullCriticalSamples.polynomial F.source u
noncomputable def active (F : Inputs) (u : List Bool) := FlatAffineFullSourceTower.free F u (F.depth u)
def direction (F : Inputs) (u : List Bool) := FlatAffineFullSourceTower.direction F u (F.depth u)
noncomputable def levels (F : Inputs) (u : List Bool) (j : Fin (arity F u)) :=
  (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial

noncomputable def ancestors (F : Inputs) (u : List Bool) (x : Fin (count F u) → ℝ) :=
  x ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)

noncomputable def slice (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u) :
    Set (Fin (arity F u) → ℝ) :=
  {y | (source F u).eval₂ (Int.castRingHom ℝ) y = 0 ∧ ∀ j ∈ active F u,
    ∑ i, (direction F u j.succ i : ℝ) * y i = (levels F u j).eval₂ (Int.castRingHom ℝ) (ancestors F u x.val)}

theorem exists_joined_label (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (hcompact : IsCompact (slice F u x))
    (hregular : ∀ y ∈ slice F u x, Function.Surjective
      (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ) (source F u) (active F u) (direction F u) y))
    (hindependent : ¬∃ c : active F u → ℝ, ∀ i,
      (direction F u 0 i : ℝ) = ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ))
    (z : Fin (arity F u) → ℝ) (hz : z ∈ slice F u x) :
    ∃ w : {w : List Bool // FlatAffineCompleteVertices.Valid (next F) hcone u w},
      JoinedIn (slice F u x) z
        (newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) hcone u w).val ∘ Sum.inl) ∧
      FlatAffineCompleteRootStages.project (next F) F.depth u (by change F.depth u ≤ F.depth u + 1; omega)
        (FlatAffineCompleteVertices.vertexEquiv (next F) hcone u w) = x := by
  obtain ⟨y, mu, _, hj, hroot⟩ := FlatAffineComponentSampling.exists_joined_stage_root (Int.castRingHom ℝ)
    (source F u) (active F u) (direction F u) (levels F u) (ancestors F u x.val)
    hcompact (fun y hp hl => hregular y ⟨hp, hl⟩) hindependent z hz.1 hz.2
  let root := FlatAffineCompleteRootStages.extend F u x (Sum.elim y mu) hroot
  let w := (FlatAffineCompleteVertices.vertexEquiv (next F) hcone u).symm root
  have hw : FlatAffineCompleteVertices.vertexEquiv (next F) hcone u w = root := Equiv.apply_symm_apply _ _
  refine ⟨w, ?_, ?_⟩
  · rw [hw, FlatAffineCompleteRootStages.extend_newest]
    exact hj
  · rw [hw]
    exact FlatAffineCompleteRootStages.extend_prefix F u x (Sum.elim y mu) hroot

end LeanCanny.Encoding.FlatAffineCompleteComponentSamples

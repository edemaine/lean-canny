/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineShiftedSliceProjection
public import LeanCanny.Geometry.ConstraintLineCharts

/-! # The actual full constraint map and its fixed coordinate line -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSliceConstraintMap
open Set LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open FlatAffineCriticalExtremum (constraint derivative)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def active (F : Inputs) (u : List Bool) := FlatAffineFullSourceTower.free F u (F.depth u)
noncomputable def table (F : Inputs) (u : List Bool) := FlatAffineFullSourceTower.direction F u (F.depth u)

noncomputable def map (F : Inputs) (u : List Bool) : (Fin (arity F u) → ℝ) → Option (active F u) → ℝ :=
  fun y j => (constraint (BoundedFullCriticalSamples.polynomial F.source u) (active F u) (table F u) j).eval₂ (Int.castRingHom ℝ) y

noncomputable def target (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u) : Option (active F u) → ℝ
  | none => 0
  | some j => (FlatAffineFullSourceTower.level F u (F.depth u) j.val).polynomial.eval₂ (Int.castRingHom ℝ)
      (x.val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u))

theorem map_none (F : Inputs) (u : List Bool) (y : Fin (arity F u) → ℝ) :
    map F u y none = (BoundedFullCriticalSamples.polynomial F.source u).eval₂ (Int.castRingHom ℝ) y := rfl

theorem map_some (F : Inputs) (u : List Bool) (y : Fin (arity F u) → ℝ) (j : active F u) :
    map F u y (some j) = ∑ i, (table F u j.val.succ i : ℝ) * y i :=
  AffineHeightPolynomial.eval (Int.castRingHom ℝ) (table F u j.val.succ) id y

theorem contDiff_map (F : Inputs) (u : List Bool) : ContDiff ℝ ⊤ (map F u) :=
  contDiff_pi.mpr (fun j => ProjectionCritical.contDiff_eval (Int.castRingHom ℝ)
    (constraint (BoundedFullCriticalSamples.polynomial F.source u) (active F u) (table F u) j))

theorem map_derivative (F : Inputs) (u : List Bool) (y : Fin (arity F u) → ℝ) :
    fderiv ℝ (map F u) y = derivative (Int.castRingHom ℝ)
      (BoundedFullCriticalSamples.polynomial F.source u) (active F u) (table F u) y := by
  apply HasFDerivAt.fderiv
  exact hasFDerivAt_pi.mpr (fun j => PolynomialCalculus.hasFDerivAt (Int.castRingHom ℝ)
    (constraint (BoundedFullCriticalSamples.polynomial F.source u) (active F u) (table F u) j) y)

theorem coarse_iff (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) (hs : h ∈ active F u) (y : Fin (arity F u) → ℝ) :
    y ∈ ConstraintLineCharts.coarseSet (map F u) (target F u x) (some ⟨h, hs⟩) ↔
      y ∈ FlatAffineShiftedSlice.coarseSlice F u x h := by
  constructor
  · intro hy
    refine ⟨hy none (by simp), ?_⟩
    intro j hj
    obtain ⟨hjh, hjs⟩ := Finset.mem_erase.mp hj
    have HN : (some (⟨j, hjs⟩ : active F u)) ≠ some ⟨h, hs⟩ := by
      intro he
      exact hjh (congrArg Subtype.val (Option.some.inj he))
    exact (map_some F u y ⟨j, hjs⟩).symm.trans (hy _ HN)
  · intro hy j hj
    cases j with
    | none => exact hy.1
    | some j =>
      have HN : j.val ≠ h := by
        intro he
        exact hj (congrArg some (Subtype.ext he))
      exact (map_some F u y j).trans (hy.2 j.val (Finset.mem_erase.mpr ⟨HN, j.property⟩))

theorem height_eq (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) (hs : h ∈ active F u) (y : Fin (arity F u) → ℝ) :
    map F u y (some ⟨h, hs⟩) - target F u x (some ⟨h, hs⟩) = FlatAffineShiftedSlice.heightValue F u x h y :=
  congrArg (fun q => q - target F u x (some ⟨h, hs⟩)) (map_some F u y ⟨h, hs⟩)

end LeanCanny.Encoding.FlatAffineSliceConstraintMap

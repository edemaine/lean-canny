/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineSliceConstraintMap
public import LeanCanny.Geometry.RegularFiberComponentPaths
/-! # Actual regular shifted slices have paths inside every connected component -/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineRegularSlicePaths
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineSliceConstraintMap (active map target)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem slice_eq_fiber (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) (hh : h ∈ active F u) (t : ℝ) :
    FlatAffineShiftedSlice.slice F u x h t = {y | map F u y = target F u x + Pi.single (some ⟨h,hh⟩) t} := by
  ext y
  constructor
  · intro HY
    funext j
    cases j with
    | none => simpa only [FlatAffineSliceConstraintMap.map_none, target, Pi.add_apply, Pi.single_apply, reduceCtorEq, ite_false, add_zero] using HY.1
    | some j =>
      simpa only [FlatAffineSliceConstraintMap.map_some, FlatAffineSliceConstraintMap.table, target, Pi.add_apply, Pi.single_apply, Option.some.injEq, Subtype.ext_iff] using HY.2 j.val j.property
  · intro HY
    constructor
    · have H := congrFun HY none
      simpa only [FlatAffineSliceConstraintMap.map_none, target, Pi.add_apply, Pi.single_apply, reduceCtorEq, ite_false, add_zero] using H
    · intro j hj
      have H := congrFun HY (some ⟨j,hj⟩)
      simpa only [FlatAffineSliceConstraintMap.map_some, FlatAffineSliceConstraintMap.table, target, Pi.add_apply, Pi.single_apply, Option.some.injEq, Subtype.ext_iff] using H

theorem locallyPathConnected (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) (hh : h ∈ active F u) (t : ℝ)
    (HR : ∀ y ∈ FlatAffineShiftedSlice.slice F u x h t, Function.Surjective
      (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ) (BoundedFullCriticalSamples.polynomial F.source u)
        (active F u) (FlatAffineFullSourceTower.direction F u (F.depth u)) y)) :
    LocallyPathConnectedSpace (FlatAffineShiftedSlice.slice F u x h t) := by
  let c := target F u x + Pi.single (some ⟨h,hh⟩) t
  have HE := slice_eq_fiber F u x h hh t
  let : LocallyPathConnectedSpace (RegularFiber.Fiber (map F u) c) := RegularFiber.locallyPathConnected (map F u) c
    (fun _ => (FlatAffineSliceConstraintMap.contDiff_map F u).contDiffAt.of_le (by simp))
    (fun y => by rw [FlatAffineSliceConstraintMap.map_derivative]; exact HR y.val (HE ▸ y.property))
  exact (Homeomorph.setCongr HE).symm.locallyPathConnectedSpace

theorem joinedIn_of_component (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) (hh : h ∈ active F u) (t : ℝ)
    (HR : ∀ y ∈ FlatAffineShiftedSlice.slice F u x h t, Function.Surjective
      (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ) (BoundedFullCriticalSamples.polynomial F.source u)
        (active F u) (FlatAffineFullSourceTower.direction F u (F.depth u)) y))
    (y : Fin (arity F u) → ℝ) (hy : y ∈ FlatAffineShiftedSlice.slice F u x h t)
    (z : Fin (arity F u) → ℝ) (hz : z ∈ connectedComponentIn (FlatAffineShiftedSlice.slice F u x h t) y) :
    JoinedIn (FlatAffineShiftedSlice.slice F u x h t) y z := by
  let : LocallyPathConnectedSpace (FlatAffineShiftedSlice.slice F u x h t) := locallyPathConnected F u x h hh t HR
  exact RegularFiberComponentPaths.joinedIn_of_component _ y hy z hz

end LeanCanny.Connectivity.FlatAffineRegularSlicePaths

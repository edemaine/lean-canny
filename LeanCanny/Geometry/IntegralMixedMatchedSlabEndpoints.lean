/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedMatchedSlabInterior
public import LeanCanny.Geometry.IntegralMixedJointBranchEndpointRecord
/-! # All matched anchors use the same recursive endpoint fibers -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι κ L R : Type}

namespace MatchedSlabInterior
variable {x : State P S B m ι} {hm : m≤S}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {F : Frame n}
    {h : Fin (n+1)} {hh : h∈F.frozen} {g : Fin (n+1)} {hg : g∉F.frozen}
    {values : Fin m→ℝ} {a b : ℝ} {t₀ : Ioo a b}
    (M : MatchedSlabInterior x hm φ F h hh g hg values a b t₀)

theorem left_endpoints_joined
    (left : ClopenPathCover ((coarseProjection P F values h) ⁻¹' {a}) L)
    (i j : IntegralMixedSelectedPhysicalFiber.physical
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ t₀.val)
    (Hmid : JoinedIn (shiftedSlice P F values h t₀.val)
      (i.val∘(FrozenCoordinateOrdering.permutation F.frozen).symm)
      (j.val∘(FrozenCoordinateOrdering.permutation F.frozen).symm)) :
    JoinedIn (shiftedSlice P F values h a)
      (M.curve i a∘(FrozenCoordinateOrdering.permutation F.frozen).symm)
      (M.curve j a∘(FrozenCoordinateOrdering.permutation F.frozen).symm) :=by
  have hab : a<b:=t₀.property.1.trans t₀.property.2
  have HJ:=M.interior.left_endpoints_joined M.clopen hab left ((M.overlap i j).mpr Hmid)
  have HS:=(joined_fiber_iff P F values h hh a (M.interior.arc i a) (M.interior.arc j a)
    (M.interior.level_left i) (M.interior.level_left j)).mp HJ
  rw [M.readback i a ⟨le_rfl,hab.le⟩,M.readback j a ⟨le_rfl,hab.le⟩] at HS
  exact HS

theorem right_endpoints_joined
    (right : ClopenPathCover ((coarseProjection P F values h) ⁻¹' {b}) R)
    (i j : IntegralMixedSelectedPhysicalFiber.physical
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ t₀.val)
    (Hmid : JoinedIn (shiftedSlice P F values h t₀.val)
      (i.val∘(FrozenCoordinateOrdering.permutation F.frozen).symm)
      (j.val∘(FrozenCoordinateOrdering.permutation F.frozen).symm)) :
    JoinedIn (shiftedSlice P F values h b)
      (M.curve i b∘(FrozenCoordinateOrdering.permutation F.frozen).symm)
      (M.curve j b∘(FrozenCoordinateOrdering.permutation F.frozen).symm) :=by
  have hab : a<b:=t₀.property.1.trans t₀.property.2
  have HJ:=M.interior.right_endpoints_joined M.clopen hab right ((M.overlap i j).mpr Hmid)
  have HS:=(joined_fiber_iff P F values h hh b (M.interior.arc i b) (M.interior.arc j b)
    (M.interior.level_right i) (M.interior.level_right j)).mp HJ
  rw [M.readback i b ⟨hab.le,le_rfl⟩,M.readback j b ⟨hab.le,le_rfl⟩] at HS
  exact HS

end MatchedSlabInterior

end LeanCanny.Geometry.IntegralMixedFrozenFrame

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameHeightCut
public import LeanCanny.Geometry.CoordinateConstraintSingularity

/-! # The actual finite height cut excludes full-fiber singularities -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

def coordinateNormals (F : Frame n) : Fin (n+2)→Fin (n+1)→ℤ :=
  Fin.cons (fun _=>0) (fun j i=>if i=j then F.scales j else 0)

theorem regular_of_heightCut (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (ht : (heightCut x hm F h).eval₂ φ.toRingHom t≠0)
    (y : Fin (n+1)→ℝ) (hy : y∈shiftedSlice P F values h t) :
    Function.Surjective (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ)
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree) F.frozen (coordinateNormals F) y) := by
  by_contra HS
  apply ht
  apply heightCut_root x hm φ F h hh values H t y hy
  exact CoordinateConstraintSingularity.outside_zero _ F.frozen (coordinateNormals F) F.scales
    F.scales_ne_zero (fun _ _=>rfl) y hy.1 HS

end LeanCanny.Geometry.IntegralMixedFrozenFrame

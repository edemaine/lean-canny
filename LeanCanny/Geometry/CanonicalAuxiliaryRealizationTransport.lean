/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryFramedSample
/-! # Bank realization survives heterogeneous native metadata transport -/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra IntegralMixedHistory

theorem originalRealization_transport {a n S S' B B' m m' : ℕ} {P : SpatialSource a} {ι κ : Type}
    (x : State P S B m ι) (y : State P S' B' m' κ)
    (hS : S=S') (hB : B=B') (hm : m=m') (hindex : ι=κ) (hxy : HEq x y)
    (p : Fin n → ℝ) (hy : OriginalRealization y p) : OriginalRealization x p := by
  cases hS
  cases hB
  exact originalRealization_of_heq x y hm hindex hxy p hy
end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory

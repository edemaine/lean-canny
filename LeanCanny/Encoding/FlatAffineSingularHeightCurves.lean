/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineSingularHeightCurves
public import LeanCanny.Encoding.CoordinateAffineTower

/-! # Singular height constancy for the actual source records

The source decomposition and previous cone certificates come from the
original affine tower. At the varied stage only the coordinate normals are
required; its objective may be arbitrary. Coarsening supplies finiteness,
without a supplied finite-root or regularity premise.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSingularHeightCurves
open LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open FlatAffineCriticalTower (Level width)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]

section
variable (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F) (u : List Bool)
  (k : ℕ) (hk : k ≤ F.depth u) (h : Fin (arity F u))
  (hnormal : ∀ j i, FlatAffineFullSourceTower.direction F u k j.succ i = FermatCoordinateCone.normal j i)
  (x : T → Fin (k * stageWidth F u) → ℝ) (y : T → Fin (arity F u) → ℝ)
  (mu : T → Fin (arity F u + 1) → ℝ)
  (hx : Continuous x) (hy : Continuous y) (hmu : Continuous mu)
  (hprefix : ∀ t i, (FlatAffineCriticalTower.system (BoundedFullCriticalSamples.polynomial F.source u)
    (FlatAffineFullSourceTower.free F u) (FlatAffineFullSourceTower.direction F u)
    (FlatAffineFullSourceTower.level F u) k i).eval₂ (Int.castRingHom ℝ) (x t) = 0)
  (hz : ∀ t, mu t 0 = 0)
  (hroot : ∀ t j, j ≠ Sum.inr h.succ →
    (FlatAffineCriticalStage.row (BoundedFullCriticalSamples.polynomial F.source u)
      (FlatAffineFullSourceTower.free F u k) (FlatAffineFullSourceTower.direction F u k)
      (fun i => (FlatAffineFullSourceTower.level F u k i).polynomial) j).eval₂ (Int.castRingHom ℝ)
        (Sum.elim (x t ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) k)
          (Sum.elim (y t) (mu t))) = 0)

include cone hk hnormal hx hy hmu hprefix hz hroot in
theorem constant (r t : T) : x r = x t ∧ y r = y t := by
  have HP := hprefix
  have HR := hroot
  rw [FlatAffinePowerPositive.source_eq] at HP HR
  exact Geometry.FlatAffineSingularHeightCurves.constant (FlatAffinePowerPositive.lower F u) _
    (IntegerRegularSource.leading_ne_zero _ _ _ one_ne_zero) (FlatAffinePowerControls.degree F u)
    (BoundedRegularSource.powerDegree_gt_one (BoundedFullWriter.size F.source u))
    (FlatAffinePowerPositive.lower_degree F u) (FlatAffineFullSourceTower.free F u)
    (FlatAffineFullSourceTower.direction F u) (FlatAffineFullSourceTower.level F u) h hnormal
    (fun t => cone u ⟨t.val, t.isLt.trans_le hk⟩) x y mu hx hy hmu HP hz HR r t

include cone hk hnormal hx hy hmu hprefix hz hroot in
theorem height_constant (hactive : h ∈ FlatAffineFullSourceTower.free F u k)
    (parameter : T → ℝ)
    (heq : ∀ t, (FlatAffineCriticalStage.row (BoundedFullCriticalSamples.polynomial F.source u)
      (FlatAffineFullSourceTower.free F u k) (FlatAffineFullSourceTower.direction F u k)
      (fun i => (FlatAffineFullSourceTower.level F u k i).polynomial) (Sum.inr h.succ)).eval₂ (Int.castRingHom ℝ)
        (Sum.elim (x t ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) k)
          (Sum.elim (y t) (mu t))) = parameter t) (r t : T) : parameter r = parameter t := by
  obtain ⟨HX, HY⟩ := constant F cone u k hk h hnormal x y mu hx hy hmu hprefix hz hroot r t
  exact (heq r).symm.trans ((Geometry.FlatAffineSingularHeightCurves.height_value_eq _ _ _ _ h hactive
    _ _ (y r) (y t) (mu r) (mu t) (congrArg (fun f => f ∘
      TriangularPolynomialIndexing.enumerate (stageWidth F u) k) HX) HY).trans (heq t))
end

end LeanCanny.Encoding.FlatAffineSingularHeightCurves

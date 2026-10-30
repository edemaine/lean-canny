/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineScaledCoordinateCoarsening
public import LeanCanny.Encoding.FlatAffinePowerInfinity

/-! # Finite coarser roots from actual scaled coordinate source records -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineScaledCoarserRoots
open LeanCanny.Algebra LeanCanny.Geometry MvPolynomial FlatAffineCriticalTower FlatAffineTowerCoarsening
open FlatAffineFullSourceTower (Inputs arity)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

theorem finite_roots (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (u : List Bool) (k : ℕ) (hk : k ≤ F.depth u) (h : Fin (arity F u))
    (scale : Fin (arity F u) → ℤ) (hscale : ∀ j, scale j ≠ 0)
    (hnormal : ∀ j i, FlatAffineFullSourceTower.direction F u k j.succ i = scale j * FermatCoordinateCone.normal j i) :
    {z : Fin ((k + 1) * width (arity F u)) → ℝ | ∀ i,
      (FlatAffineCriticalTower.system (BoundedFullCriticalSamples.polynomial F.source u)
        (active (FlatAffineFullSourceTower.free F u) k h) (directions (FlatAffineFullSourceTower.direction F u) k h)
        (FlatAffineFullSourceTower.level F u) (k + 1) i).eval₂ (Int.castRingHom ℝ) z = 0}.Finite := by
  have H := FlatAffineScaledCoordinateCoarsening.finite_roots (FlatAffinePowerPositive.lower F u) _
    (IntegerRegularSource.leading_ne_zero _ _ _ one_ne_zero) (FlatAffinePowerControls.degree F u)
    (BoundedRegularSource.powerDegree_gt_one (BoundedFullWriter.size F.source u)) (FlatAffinePowerPositive.lower_degree F u)
    scale hscale (FlatAffineFullSourceTower.free F u) (FlatAffineFullSourceTower.direction F u)
    (FlatAffineFullSourceTower.level F u) h hnormal (fun t => cone u ⟨t.val, t.isLt.trans_le hk⟩)
  rw [FlatAffinePowerPositive.source_eq]
  exact H

end LeanCanny.Encoding.FlatAffineScaledCoarserRoots

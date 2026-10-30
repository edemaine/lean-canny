/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineShiftedSingularLift

/-! # Compactness of the actual varying-height slices -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineShiftedSlice
open Set LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

theorem compact (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) (v : ℝ) : IsCompact (slice F u x h v) := by
  have HP : IsCompact {y : Fin (arity F u) → ℝ |
      (BoundedFullCriticalSamples.polynomial F.source u).eval₂ (Int.castRingHom ℝ) y = 0} := by
    have H := (BoundedFullCriticalSamples.source_proper F.source u).isCompact_preimage (isCompact_singleton (x := (0 : ℝ)))
    have HE : (fun y : Fin (F.source.dim u + 4) → ℝ => (BoundedFullCriticalSamples.realPolynomial F.source u).eval y) =
        (fun y => (BoundedFullCriticalSamples.polynomial F.source u).eval₂ (Int.castRingHom ℝ) y) := by
      funext y
      exact MvPolynomial.eval_map (Int.castRingHom ℝ) y (BoundedFullCriticalSamples.polynomial F.source u)
    rw [HE] at H
    exact H
  have HC : IsClosed {y : Fin (arity F u) → ℝ | ∀ j ∈ FlatAffineFullSourceTower.free F u (F.depth u),
      (∑ i, (FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i : ℝ) * y i) =
        (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial.eval₂ (Int.castRingHom ℝ)
          (x.val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)) + if j = h then v else 0} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro _
    exact isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))) continuous_const
  exact HP.inter_right HC

end LeanCanny.Encoding.FlatAffineShiftedSlice

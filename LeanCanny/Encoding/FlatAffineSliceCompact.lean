/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineCompleteComponentSamples

/-! # Compactness of every actual frozen affine slice

The generated original polynomial is proper. Its zero set is compact, and
the frozen affine height constraints cut out a closed subset. Compactness
therefore follows from the original source construction at every parent.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSliceCompact
open Set LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteComponentSamples (source active direction levels ancestors slice)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

theorem compact (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u) :
    IsCompact (slice F u x) := by
  have HP : IsCompact {y : Fin (arity F u) → ℝ | (source F u).eval₂ (Int.castRingHom ℝ) y = 0} := by
    have H := (BoundedFullCriticalSamples.source_proper F.source u).isCompact_preimage (isCompact_singleton (x := (0 : ℝ)))
    have HE : (fun y : Fin (F.source.dim u + 4) → ℝ => (BoundedFullCriticalSamples.realPolynomial F.source u).eval y) =
        (fun y => (BoundedFullCriticalSamples.polynomial F.source u).eval₂ (Int.castRingHom ℝ) y) := by
      funext y
      exact MvPolynomial.eval_map (Int.castRingHom ℝ) y (BoundedFullCriticalSamples.polynomial F.source u)
    rw [HE] at H
    exact H
  have HC : IsClosed {y : Fin (arity F u) → ℝ | ∀ j ∈ active F u,
      ∑ i, (direction F u j.succ i : ℝ) * y i =
        (levels F u j).eval₂ (Int.castRingHom ℝ) (ancestors F u x.val)} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro _
    exact isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))) continuous_const
  exact HP.inter_right HC

end LeanCanny.Encoding.FlatAffineSliceCompact

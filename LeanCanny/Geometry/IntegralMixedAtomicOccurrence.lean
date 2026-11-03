/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHistory
/-! # Numerical atomic occurrences in a frozen coordinate slice -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedAtomicOccurrence
open LeanCanny.Algebra IntegralMixedHistory

structure Occurrence {n :ℕ} (P :SpatialSource n) (k :ℕ) (levels :ℕ→ℝ) (p :Fin (n+1)→ℝ) :Prop where
  depth_le : k ≤ n
  zero :(FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p=0
  frozen :∀ (i :Fin (n+1)), i.val < k → p i=levels i.val
  critical :∀ (i :Fin (n+1)), k ≤ i.val → i.val≠k →
    (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
      (Int.castRingHom ℝ) p=0

end LeanCanny.Geometry.IntegralMixedAtomicOccurrence

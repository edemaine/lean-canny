/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCoordinateRename
public import Mathlib.Algebra.MvPolynomial.PDeriv
/-! # Literal derivative transport under mixed spatial coordinate permutations -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCoordinateRename
open MvPolynomial IntegralMixedHistory
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem source_rename (P : SpatialSource n) (e : Equiv.Perm (Fin (n+1))) :
    FermatCriticalHomogenization.polynomial (spatial P e).low (spatial P e).leading (spatial P e).degree =
      rename e.symm (FermatCriticalHomogenization.polynomial P.low P.leading P.degree) := by
  simp only [spatial, FermatCriticalHomogenization.polynomial, map_add, map_mul, rename_C, map_sum, map_pow, rename_X]
  congr 2
  exact (e.symm.sum_comp (fun i => (X i : MvPolynomial (Fin (n+1)) ℤ) ^ P.degree)).symm

theorem derivative_eval (P : SpatialSource n) (e : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) (y : Fin (n+1) → ℝ) :
    (pderiv i (FermatCriticalHomogenization.polynomial (spatial P e).low (spatial P e).leading (spatial P e).degree)).eval₂
      (Int.castRingHom ℝ) y =
    (pderiv (e i) (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) (y ∘ e.symm) := by
  rw [source_rename, ← e.symm_apply_apply i, pderiv_rename e.symm.injective, e.apply_symm_apply, eval₂_rename]

end LeanCanny.Algebra.IntegralMixedCoordinateRename

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHistory
/-! # Spatial coordinate permutations retain the literal mixed coefficient bank -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCoordinateRename
open IntegralMixedHistory MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def spatial (P : SpatialSource n) (e : Equiv.Perm (Fin (n+1))) : SpatialSource n where
  low := MvPolynomial.rename e.symm P.low
  leading := P.leading
  degree := P.degree
  degree_two := P.degree_two
  low_degree := (MvPolynomial.totalDegree_rename_le _ _).trans_lt P.low_degree
  leading_ne_zero := P.leading_ne_zero

noncomputable def state (x : State P S B m ι) (e : Equiv.Perm (Fin (n+1))) : State (spatial P e) S B m ι where
  sampler := x.sampler
  bank := x.bank
  denominator_ne_zero := x.denominator_ne_zero
  critical_cap := x.critical_cap

theorem expression_eq (x : State P S B m ι) (e : Equiv.Perm (Fin (n+1))) (a : AffineExpr) :
    expression (state x e) a = expression x a := by
  induction a with
  | constant c => rfl
  | reference j => rfl
  | add a b ha hb => exact congrArg₂ (· + ·) ha hb
  | scale c a ha => exact congrArg ((c : x.sampler.scalarPrefix.carrier) * ·) ha

theorem source_eval (P : SpatialSource n) (e : Equiv.Perm (Fin (n+1))) (z : Fin (n+1) → ℝ) :
    (FermatCriticalHomogenization.polynomial (spatial P e).low (spatial P e).leading (spatial P e).degree).eval₂
      (Int.castRingHom ℝ) z =
    (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) (z ∘ e.symm) := by
  simp only [spatial, FermatCriticalHomogenization.polynomial, eval₂_add, eval₂_rename, eval₂_mul,
    eval₂_C, eval₂_sum, eval₂_pow, eval₂_X, Function.comp_apply]
  congr 2
  exact (e.symm.sum_comp (fun i => z i ^ P.degree)).symm

end LeanCanny.Algebra.IntegralMixedCoordinateRename

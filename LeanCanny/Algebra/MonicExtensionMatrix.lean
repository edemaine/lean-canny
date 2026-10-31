/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCoordinateBasis

/-! # Constructed companion matrices for arbitrary monic scalar extensions

Shift columns are identities. The last column reads the original monic
equation coefficients, including over nonreduced coefficient rings.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCoordinateBasis
open Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] [Nontrivial A] {N : ℕ}

theorem relativeBasis_repr (p : Polynomial A) (hp : p.Monic) (hdeg : p.natDegree = N) (q : Polynomial A) (i : Fin N) :
    (relativeBasis p hp hdeg).repr (AdjoinRoot.mk p q) i = (q %ₘ p).coeff i.val := by
  simp only [relativeBasis, Module.Basis.repr_reindex_apply]
  change (AdjoinRoot.modByMonicHom hp (AdjoinRoot.mk p q)).coeff i.val = _
  rw [AdjoinRoot.modByMonicHom_mk]

theorem top_power_remainder (p : Polynomial A) (hp : p.Monic) (hdeg : p.natDegree = N) :
    X ^ N %ₘ p = X ^ N - p := by
  have HD : (X ^ N - p).degree < p.degree := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero, hdeg]
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro i hi
    have HN : N ≤ i := by exact_mod_cast hi
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    by_cases he : i = N
    · subst i
      rw [ite_eq_left rfl, ← hdeg, Polynomial.coeff_natDegree, hp.leadingCoeff, sub_self]
    · rw [ite_eq_right he, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), sub_self]
  have H := (Polynomial.modByMonic_eq_self_iff hp).mpr HD
  rw [Polynomial.sub_modByMonic, Polynomial.modByMonic_self hp, sub_zero] at H
  exact H

theorem relative_root_matrix (p : Polynomial A) (hp : p.Monic) (hdeg : p.natDegree = N) (i j : Fin N) :
    Algebra.leftMulMatrix (relativeBasis p hp hdeg) (AdjoinRoot.root p) i j =
      if j.val + 1 < N then (if i.val = j.val + 1 then 1 else 0) else -p.coeff i.val := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, relativeBasis_apply, ← pow_succ']
  have HM : AdjoinRoot.root p ^ (j.val + 1) = AdjoinRoot.mk p (X ^ (j.val + 1)) := by
    rw [map_pow, AdjoinRoot.mk_X]
  rw [HM, relativeBasis_repr]
  by_cases hj : j.val + 1 < N
  · rw [ite_eq_left hj, (Polynomial.modByMonic_eq_self_iff hp).mpr]
    · exact Polynomial.coeff_X_pow _ _
    · rw [Polynomial.degree_eq_natDegree hp.ne_zero, hdeg, Polynomial.degree_X_pow]
      exact_mod_cast hj
  · have HJ : j.val + 1 = N := by have := j.isLt; omega
    rw [ite_eq_right hj, HJ, top_power_remainder p hp hdeg, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, ite_eq_right (by have := i.isLt; omega), zero_sub]

theorem tower_root_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ A)
    (p : Polynomial A) (hp : p.Monic) (hdeg : p.natDegree = N) (i j : ι × Fin N) :
    Algebra.leftMulMatrix (b.smulTower (relativeBasis p hp hdeg)) (AdjoinRoot.root p) i j =
      if j.2.val + 1 < N then (if i.2.val = j.2.val + 1 then (if i.1 = j.1 then 1 else 0) else 0)
      else -Algebra.leftMulMatrix b (p.coeff i.2.val) i.1 j.1 := by
  rw [Algebra.smulTower_leftMulMatrix, relative_root_matrix]
  split_ifs <;> simp_all

end LeanCanny.Algebra.IntegralCoordinateBasis

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralParameterExtension

/-! # Multiplication matrices for monic scalar height extensions

The new generator has the usual shift columns and one normalization column.
Restricting scalars expands each coefficient to its old multiplication
matrix, so no table for the extended algebra has to be supplied.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralParameterExtension
open Polynomial Module
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [CommRing A] [Nontrivial A]

theorem relativeBasis_apply (p : Polynomial A) (d : ℕ) (i : Fin d) :
    relativeBasis p d i = AdjoinRoot.root (FixedDegreeIntegralNormalization.polynomial p d) ^ i.val := by
  simp only [relativeBasis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

theorem relativeBasis_repr_mk (p : Polynomial A) (d : ℕ) (q : Polynomial A) (i : Fin d) :
    (relativeBasis p d).repr (AdjoinRoot.mk _ q) i =
      (q %ₘ FixedDegreeIntegralNormalization.polynomial p d).coeff i.val := by
  simp only [relativeBasis, Basis.repr_reindex_apply]
  change (AdjoinRoot.modByMonicHom (FixedDegreeIntegralNormalization.monic p d)
    (AdjoinRoot.mk _ q)).coeff i.val = _
  rw [AdjoinRoot.modByMonicHom_mk]

theorem top_power_remainder (p : Polynomial A) (d : ℕ) :
    X ^ d %ₘ FixedDegreeIntegralNormalization.polynomial p d =
      X ^ d - FixedDegreeIntegralNormalization.polynomial p d := by
  let f := FixedDegreeIntegralNormalization.polynomial p d
  have hf : f.Monic := FixedDegreeIntegralNormalization.monic p d
  have hdeg : (X ^ d - f).degree < f.degree := by
    rw [Polynomial.degree_eq_natDegree hf.ne_zero, FixedDegreeIntegralNormalization.natDegree]
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro k hk
    have hdk : d ≤ k := by exact_mod_cast hk
    change (X ^ d - FixedDegreeIntegralNormalization.polynomial p d).coeff k = 0
    by_cases he : k = d
    · subst k
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow_self,
        FixedDegreeIntegralNormalization.coefficient_top, sub_self]
    · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, ite_eq_right he,
        FixedDegreeIntegralNormalization.coefficient_above p d k (by omega), sub_self]
  have H := (Polynomial.modByMonic_eq_self_iff hf).mpr hdeg
  rw [Polynomial.sub_modByMonic, Polynomial.modByMonic_self hf, sub_zero] at H
  exact H

theorem root_matrix (p : Polynomial A) (d : ℕ) (i j : Fin d) :
    Algebra.leftMulMatrix (relativeBasis p d) (AdjoinRoot.root _) i j =
      if j.val + 1 < d then (if i.val = j.val + 1 then 1 else 0)
      else -(p.coeff i.val * p.coeff d ^ (d - 1 - i.val)) := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, relativeBasis_apply, ← pow_succ']
  have HM : AdjoinRoot.root (FixedDegreeIntegralNormalization.polynomial p d) ^ (j.val + 1) =
      AdjoinRoot.mk _ (X ^ (j.val + 1)) := by
    rw [map_pow, AdjoinRoot.mk_X]
  rw [HM, relativeBasis_repr_mk]
  by_cases hj : j.val + 1 < d
  · rw [ite_eq_left hj, (Polynomial.modByMonic_eq_self_iff (FixedDegreeIntegralNormalization.monic p d)).mpr]
    · simp only [Polynomial.coeff_X_pow]
    · rw [Polynomial.degree_eq_natDegree (FixedDegreeIntegralNormalization.monic p d).ne_zero,
        FixedDegreeIntegralNormalization.natDegree, Polynomial.degree_X_pow]
      exact_mod_cast hj
  · have ht : j.val + 1 = d := by omega
    rw [ite_eq_right hj, ht, top_power_remainder, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, ite_eq_right (by omega), zero_sub,
      FixedDegreeIntegralNormalization.coefficient, ite_eq_right (by omega), ite_eq_left i.isLt, zero_add]

theorem basis_root_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) (i j : ι × Fin d) :
    Algebra.leftMulMatrix (basis b p d) (AdjoinRoot.root _) i j =
      if j.2.val + 1 < d then (if i.2.val = j.2.val + 1 then (if i.1 = j.1 then 1 else 0) else 0)
      else -Algebra.leftMulMatrix b (p.coeff i.2.val * p.coeff d ^ (d - 1 - i.2.val)) i.1 j.1 := by
  rw [basis, Algebra.smulTower_leftMulMatrix, root_matrix]
  split_ifs <;> simp_all

theorem basis_root_matrix_of_coefficients {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) (i j : ι × Fin d) :
    Algebra.leftMulMatrix (basis b p d) (AdjoinRoot.root _) i j =
      if j.2.val + 1 < d then (if i.2.val = j.2.val + 1 then (if i.1 = j.1 then 1 else 0) else 0)
      else -(Algebra.leftMulMatrix b (p.coeff i.2.val) *
        Algebra.leftMulMatrix b (p.coeff d) ^ (d - 1 - i.2.val)) i.1 j.1 := by
  rw [basis_root_matrix, map_mul, map_pow]

end LeanCanny.Algebra.IntegralParameterExtension

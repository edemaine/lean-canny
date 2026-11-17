/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Norms of polynomial values as products over characteristic roots

Factoring the test polynomial and using the symmetry of the resultant
proves the spectral product identity without triangularizing a matrix.
-/

public section

namespace LeanCanny.CountingHierarchy

open Module Polynomial
open scoped Classical BigOperators

variable {K A ι : Type*} [Field K] [CommRing A] [Algebra K A]
    [Fintype ι] [DecidableEq ι]

theorem norm_sub_algebraMap_charpoly (b : Basis ι K A) (v : A) (c : K) :
    Algebra.norm K (v - algebraMap K A c) =
      (-1 : K) ^ Fintype.card ι * (Algebra.leftMulMatrix b v).charpoly.eval c := by
  rw [Algebra.norm_eq_matrix_det b, map_sub, (Algebra.leftMulMatrix b).commutes c]
  change (Algebra.leftMulMatrix b v - Matrix.scalar ι c).det = _
  rw [← neg_sub (Matrix.scalar ι c) (Algebra.leftMulMatrix b v), Matrix.det_neg,
    ← Matrix.eval_charpoly]

/-- A norm of a polynomial value is a resultant with the characteristic
 polynomial. Only the test polynomial needs to split in the field. -/
theorem norm_aeval_eq_resultant (b : Basis ι K A) (v : A) (g : K[X]) (hg : g.Splits) :
    Algebra.norm K (Polynomial.aeval v g) =
      (Algebra.leftMulMatrix b v).charpoly.resultant g := by
  let q := (Algebra.leftMulMatrix b v).charpoly
  have hqdeg : q.natDegree = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim _
  have hn : Algebra.norm K (Polynomial.aeval v g) =
      g.leadingCoeff ^ Fintype.card ι *
        (g.roots.map (fun c => (-1 : K) ^ Fintype.card ι * q.eval c)).prod := by
    conv_lhs => rw [hg.eq_prod_roots]
    simp only [map_mul, Polynomial.aeval_C, map_multiset_prod, Multiset.map_map,
      Function.comp_apply, map_sub, Polynomial.aeval_X,
      Algebra.norm_algebraMap_of_basis b, norm_sub_algebraMap_charpoly b, q]
  rw [hn, Polynomial.resultant_comm]
  rw [Polynomial.resultant_eq_prod_eval g q q.natDegree (Nat.le_refl _) hg, hqdeg]
  rw [Multiset.prod_map_mul]
  simp only [Multiset.map_const', Multiset.prod_replicate, ← pow_mul,
    ← hg.natDegree_eq_card_roots]
  rw [mul_comm (Fintype.card ι) g.natDegree]
  ring

/-- The norm is the product of the test values at the characteristic
 roots, counted with multiplicity. This includes singular algebras. -/
theorem norm_aeval_eq_prod_charpoly_roots (b : Basis ι K A) (v : A) (g : K[X])
    (hg : g.Splits) (hq : (Algebra.leftMulMatrix b v).charpoly.Splits) :
    Algebra.norm K (Polynomial.aeval v g) =
      ((Algebra.leftMulMatrix b v).charpoly.roots.map g.eval).prod := by
  rw [norm_aeval_eq_resultant b v g hg, Polynomial.resultant_eq_prod_eval _ _ _ (Nat.le_refl _) hq,
    ((Algebra.leftMulMatrix b v).charpoly_monic).leadingCoeff, one_pow, one_mul]

end LeanCanny.CountingHierarchy

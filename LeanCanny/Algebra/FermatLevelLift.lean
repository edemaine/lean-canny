/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHistory
public import LeanCanny.Algebra.FermatCriticalHomogenization

/-! # A bounded free level coordinate with the original Fermat degree

Appending the free objective v changes LOW by -A*v. Every original physical
coordinate and the frozen prefix retain their literal order. The coefficient
A is an integer source coefficient, not another frozen height.
-/
@[expose] public section
namespace LeanCanny.Algebra.FermatLevelLift
open MvPolynomial
open scoped BigOperators
variable {n : ℕ}

noncomputable def source (P : IntegralMixedHistory.SpatialSource n) (A : ℤ) :
    IntegralMixedHistory.SpatialSource (n+1) where
  low := rename Fin.castSucc P.low-C A*X (Fin.last (n+1))
  leading := P.leading
  degree := P.degree
  degree_two := P.degree_two
  low_degree := (totalDegree_sub _ _).trans_lt (max_lt
    ((MvPolynomial.totalDegree_rename_le _ _).trans_lt P.low_degree)
    ((totalDegree_mul _ _).trans_lt (by simp only [totalDegree_C,zero_add,totalDegree_X]; have H:=P.degree_two; omega)))
  leading_ne_zero := P.leading_ne_zero

noncomputable def polynomial (P : IntegralMixedHistory.SpatialSource n) : MvPolynomial (Fin (n+1)) ℤ :=
  FermatCriticalHomogenization.polynomial P.low P.leading P.degree

theorem eval_source {R : Type*} [CommRing R] (P : IntegralMixedHistory.SpatialSource n)
    (A : ℤ) (x : Fin (n+1) → R) (v : R) :
    (polynomial (source P A)).eval₂ (Int.castRingHom R) (Fin.snoc x v) =
      (polynomial P).eval₂ (Int.castRingHom R) x + (P.leading:R)*v^P.degree-(A:R)*v := by
  simp only [polynomial,FermatCriticalHomogenization.polynomial,source,eval₂_add,eval₂_sub,eval₂_mul,
    eval₂_C,eval₂_X,eval₂_rename,eval₂_sum,eval₂_pow,Fin.sum_univ_castSucc,Fin.snoc_last,Fin.snoc_castSucc,Int.coe_castRingHom]
  have HC : (Fin.snoc x v) ∘ Fin.castSucc=x := by funext i; simp
  rw [HC]
  ring

theorem polynomial_eq (P : IntegralMixedHistory.SpatialSource n) (A : ℤ) :
    polynomial (source P A) = rename Fin.castSucc (polynomial P) +
      C P.leading*X (Fin.last (n+1))^P.degree-C A*X (Fin.last (n+1)) := by
  simp only [polynomial,source,FermatCriticalHomogenization.polynomial,map_add,map_mul,
    rename_C,map_sum,map_pow,rename_X,Fin.sum_univ_castSucc]
  ring

theorem derivative (P : IntegralMixedHistory.SpatialSource n) (A : ℤ) (i : Fin (n+1)) :
    pderiv i.castSucc (polynomial (source P A)) = rename Fin.castSucc (pderiv i (polynomial P)) := by
  rw [polynomial_eq]
  simp [pderiv_rename (Fin.castSucc_injective (n+1)),Fin.castSucc_ne_last]

end LeanCanny.Algebra.FermatLevelLift

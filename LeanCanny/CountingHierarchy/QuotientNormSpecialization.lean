/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.NormPolynomialEvaluation
public import LeanCanny.CountingHierarchy.PowerTraceCharacteristic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Spectral products for source quotient determinants -/

public section

namespace LeanCanny.CountingHierarchy.PurePowerResidue

open Polynomial MvPolynomial Module
open scoped BigOperators Classical

/-- Power-trace specialization also identifies the actual source determinant. -/
theorem multiplicationMatrix_det_map {S K : Type*} [CommRing S] [Field K]
    {n : ℕ} (φ : S →+* K) (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) S)
    (hK : ∀ j, 1 ≤ j → j ≤ (d + 1) ^ n → (j : K) ≠ 0) :
    φ ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).det) =
      (multiplicationMatrix (by omega : 1 ≤ d + 1) (fun i => (r i).map φ)
        (fun i => (map_degree_le φ _).trans_lt ((hr i).trans_lt (Nat.lt_succ_self d)))
        (v.map φ)).det := by
  have h := congrArg (fun p : Polynomial K => p.coeff 0)
    (multiplicationMatrix_charpoly_map φ d hd r hr v hK)
  simp only [Polynomial.coeff_map] at h
  rw [Matrix.det_eq_sign_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff]
  simp only [map_mul, map_pow, map_neg, map_one]
  rw [h]

/-- Over a splitting field, the determinant of multiplication by `g(v)`
 is the product of `g` at the actual characteristic roots of `v`. -/
theorem multiplicationMatrix_aeval_det_eq_prod_roots {K : Type*} [Field K]
    {n ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) K) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) K) (g : Polynomial K) (hg : g.Splits)
    (hq : (multiplicationMatrix hell r hr v).charpoly.Splits) :
    (multiplicationMatrix hell r hr (Polynomial.aeval v g)).det =
      ((multiplicationMatrix hell r hr v).charpoly.roots.map g.eval).prod := by
  let b := normalBasis hell r hr
  let π := projection ell r
  change (Algebra.leftMulMatrix b (π (Polynomial.aeval v g))).det = _
  rw [← Algebra.norm_eq_matrix_det b, ← Polynomial.aeval_algHom_apply]
  exact norm_aeval_eq_prod_charpoly_roots b (π v) g hg hq

/-- The original coefficient-ring determinant maps to the spectral product
 of its source characteristic polynomial. No quotient basis-change algorithm
 or assumed determinant oracle occurs in the statement. -/
theorem multiplicationMatrix_aeval_det_map_eq_prod_roots
    {S K : Type*} [CommRing S] [Field K] {n : ℕ}
    (φ : S →+* K) (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) S) (g : Polynomial S)
    (hK : ∀ j, 1 ≤ j → j ≤ (d + 1) ^ n → (j : K) ≠ 0)
    (hg : (g.map φ).Splits)
    (hq : ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly.map φ).Splits) :
    φ ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) (Polynomial.aeval v g)).det) =
      (((multiplicationMatrix (by omega : 1 ≤ d + 1) r
        (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly.map φ).roots.map
          (g.map φ).eval).prod := by
  rw [multiplicationMatrix_det_map φ d hd r hr _ hK]
  have hm : (Polynomial.aeval v g).map φ = Polynomial.aeval (v.map φ) (g.map φ) :=
    Polynomial.map_aeval_eq_aeval_map (φ := φ) (ψ := MvPolynomial.map φ)
      (by ext a; simp) g v
  rw [hm]
  have hchar := multiplicationMatrix_charpoly_map φ d hd r hr v hK
  rw [hchar] at hq ⊢
  exact multiplicationMatrix_aeval_det_eq_prod_roots (by omega : 1 ≤ d + 1) _ _ _ _ hg hq

end LeanCanny.CountingHierarchy.PurePowerResidue

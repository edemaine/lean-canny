/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.QuotientNormSpecialization
public import LeanCanny.CountingHierarchy.RealRootProducts

/-! # Real signs of integer quotient determinants as finite root products -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial MvPolynomial
open scoped BigOperators Classical

theorem integer_real_complex_polynomial_map (p : Polynomial ℤ) :
    (p.map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ) = p.map (Int.castRingHom ℂ) := by
  rw [Polynomial.map_map]
  congr 1

theorem integer_real_map_aeval (p : Polynomial ℤ) (z : ℂ) :
    Polynomial.aeval z (p.map (Int.castRingHom ℝ)) = (p.map (Int.castRingHom ℂ)).eval z := by
  rw [← integer_real_complex_polynomial_map p, Polynomial.eval_map]
  exact Polynomial.aeval_def (R := ℝ) (A := ℂ) (x := z) (p.map (Int.castRingHom ℝ))

namespace PurePowerResidue

/-- With simple characteristic roots, the source integer determinant has
 exactly the sign of the finite spectral product used by real-root labels. -/
theorem multiplicationMatrix_aeval_det_cast_eq_real_root_product {n : ℕ}
    (d : ℕ) (hd : 1 ≤ d) (r : Fin n → MvPolynomial (Fin n) ℤ)
    (hr : ∀ i, (r i).totalDegree ≤ d) (v : MvPolynomial (Fin n) ℤ)
    (q : Polynomial ℤ)
    (hq : q = (multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly)
    (hsep : (q.map (Int.castRingHom ℂ)).Separable) (g : Polynomial ℤ) :
    (((multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) (Polynomial.aeval v g)).det : ℤ) : ℝ) =
      (∏ z ∈ complexRootSet (q.map (Int.castRingHom ℝ)),
        Polynomial.aeval z (g.map (Int.castRingHom ℝ))).re := by
  have hK (j : ℕ) (hj : 1 ≤ j) (_hle : j ≤ (d + 1) ^ n) : (j : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : j ≠ 0)
  have he := multiplicationMatrix_aeval_det_map_eq_prod_roots (Int.castRingHom ℂ)
    d hd r hr v g hK (IsAlgClosed.splits _) (IsAlgClosed.splits _)
  rw [← hq] at he
  have hprod : (∏ z ∈ complexRootSet (q.map (Int.castRingHom ℝ)),
      Polynomial.aeval z (g.map (Int.castRingHom ℝ))) =
        ((q.map (Int.castRingHom ℂ)).roots.map (g.map (Int.castRingHom ℂ)).eval).prod := by
    simp only [complexRootSet, integer_real_complex_polynomial_map, integer_real_map_aeval]
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, (Polynomial.nodup_roots hsep).dedup]
  rw [hprod, ← he]
  simp only [Int.coe_castRingHom, Complex.intCast_re]

end PurePowerResidue
end LeanCanny.CountingHierarchy

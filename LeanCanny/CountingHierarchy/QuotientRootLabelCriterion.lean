/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SparseRootProductCriterion
public import LeanCanny.CountingHierarchy.QuotientRealSpectralProduct

/-! # One integer quotient determinant detects a real root below a cutoff -/

public section

namespace LeanCanny.CountingHierarchy.PurePowerResidue

open Polynomial MvPolynomial LeanCanny.Algebra
open scoped Classical

/-- The short label and shift are the only existential witnesses. The
 determinant is the actual source quotient multiplication determinant. -/
theorem root_below_iff_negative_quotient_label {n : ℕ}
    (d : ℕ) (hd : 1 ≤ d) (r : Fin n → MvPolynomial (Fin n) ℤ)
    (hr : ∀ i, (r i).totalDegree ≤ d) (v : MvPolynomial (Fin n) ℤ)
    (q : Polynomial ℤ)
    (hq : q = (multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly)
    (hsep : (q.map (Int.castRingHom ℂ)).Separable)
    (N b : ℕ) (hDN : (d + 1) ^ n ≤ 2 ^ N) (R : ℤ)
    (hqm : coefficientMass q ≤ 2 ^ b)
    (hRm : coefficientMass (Polynomial.C R - Polynomial.X) ≤ 2 ^ b) :
    (∃ x : ℝ, q.eval₂ (Int.castRingHom ℝ) x = 0 ∧ x < R) ↔
      ∃ L : List (Fin ((d + 1) ^ n) × SignType), L.length ≤ N ∧ ∃ e : ℕ, e ≤ (d + 1) ^ n ∧
        (multiplicationMatrix (by omega : 1 ≤ d + 1) r
          (fun i => (hr i).trans_lt (Nat.lt_succ_self d))
          (Polynomial.aeval v (shiftedIntegerLabel ((d + 1) ^ n) e
            (sparseIntegerRootLabel q (Polynomial.C R - Polynomial.X) N b L)))).det < 0 := by
  have hqmonic : q.Monic := hq ▸ Matrix.charpoly_monic _
  have hD : q.natDegree = (d + 1) ^ n := by
    rw [hq, Matrix.charpoly_natDegree_eq_dim, card_normalIndex]
  have hDpos : 1 ≤ (d + 1) ^ n := Nat.one_le_pow _ _ (by omega)
  have h := root_below_iff_negative_sparse_product q hqmonic.ne_zero hDpos hD.le N b hDN R hqm hRm
  constructor
  · intro hx
    obtain ⟨L, hL, e, he, hprod⟩ := h.mp hx
    refine ⟨L, hL, e, he, ?_⟩
    have hv := multiplicationMatrix_aeval_det_cast_eq_real_root_product d hd r hr v q hq hsep
      (shiftedIntegerLabel ((d + 1) ^ n) e (sparseIntegerRootLabel q (Polynomial.C R - Polynomial.X) N b L))
    rw [← hv] at hprod
    exact_mod_cast hprod
  · rintro ⟨L, hL, e, he, hneg⟩
    apply h.mpr
    refine ⟨L, hL, e, he, ?_⟩
    have hv := multiplicationMatrix_aeval_det_cast_eq_real_root_product d hd r hr v q hq hsep
      (shiftedIntegerLabel ((d + 1) ^ n) e (sparseIntegerRootLabel q (Polynomial.C R - Polynomial.X) N b L))
    rw [← hv]
    exact_mod_cast hneg

end LeanCanny.CountingHierarchy.PurePowerResidue

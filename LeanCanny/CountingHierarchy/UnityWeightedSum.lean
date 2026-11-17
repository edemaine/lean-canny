/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.UnityRootSeparation
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Tactic.NormNum

/-! # Geometric weights distinguish tuples of roots of unity -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial
open scoped Classical BigOperators NNReal

/-- A coefficient polynomial of the difference of two root tuples has
 coefficient norms at most two and leading coefficient norm at least
 `1/ell`. Cauchy's root bound therefore excludes every integer base at
 least `2*ell+1`. -/
theorem unity_weightedSum_injective (ell : ℕ) (hell : ell ≠ 0) (R : ℕ)
    (hR : 2 * ell + 1 ≤ R) (n : ℕ) (z w : Fin n → ℂ)
    (hz : ∀ i, z i ^ ell = 1) (hw : ∀ i, w i ^ ell = 1)
    (hsum : (∑ i, (R : ℂ) ^ i.val * z i) = ∑ i, (R : ℂ) ^ i.val * w i) : z = w := by
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ w i := by simpa only [funext_iff, not_forall] using hne
  let P : ℂ[X] := Polynomial.ofFn n (fun i => z i - w i)
  have hP : P ≠ 0 := by
    intro h
    have hc := congrArg (fun p : ℂ[X] => p.coeff i.val) h
    rw [show P.coeff i.val = z i - w i from ofFn_coeff_eq_val_of_lt _ i.isLt,
      Polynomial.coeff_zero] at hc
    exact hi (sub_eq_zero.mp hc)
  have hdeg : P.natDegree < n := ofFn_natDegree_lt (by have := i.isLt; omega) _
  have hcoeff (k : ℕ) : ‖P.coeff k‖₊ ≤ (2 : ℝ≥0) := by
    by_cases hk : k < n
    · have hc : P.coeff k = z ⟨k, hk⟩ - w ⟨k, hk⟩ := ofFn_coeff_eq_val_of_lt _ hk
      apply NNReal.coe_le_coe.mp
      simp only [coe_nnnorm, NNReal.coe_ofNat, hc]
      exact (norm_sub_le _ _).trans_eq (by
        rw [Complex.norm_eq_one_of_pow_eq_one (hz _) hell,
          Complex.norm_eq_one_of_pow_eq_one (hw _) hell]; norm_num)
    · rw [show P.coeff k = 0 from ofFn_coeff_eq_zero_of_ge _ (by omega)]
      simp
  let j : Fin n := ⟨P.natDegree, hdeg⟩
  have hlead : P.leadingCoeff = z j - w j := by
    rw [← coeff_natDegree]
    exact ofFn_coeff_eq_val_of_lt _ hdeg
  have hj : z j ≠ w j := by
    intro h
    exact (leadingCoeff_ne_zero.mpr hP) (by rw [hlead, h, sub_self])
  have hsep : 1 ≤ (ell : ℝ≥0) * ‖P.leadingCoeff‖₊ := by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_one, NNReal.coe_mul, NNReal.coe_natCast, coe_nnnorm, hlead] using
      one_le_mul_norm_unity_sub ell hell (z j) (w j) (hz j) (hw j) hj
  have hleadpos : 0 < ‖P.leadingCoeff‖₊ := by
    exact nnnorm_pos.mpr (leadingCoeff_ne_zero.mpr hP)
  have hb : P.cauchyBound ≤ 2 * (ell : ℝ≥0) + 1 := by
    unfold Polynomial.cauchyBound
    apply add_le_add _ le_rfl
    apply (div_le_iff₀ hleadpos).mpr
    calc
      _ ≤ 2 := Finset.sup_le (fun k _ => hcoeff k)
      _ = 2 * 1 := by simp
      _ ≤ 2 * ((ell : ℝ≥0) * ‖P.leadingCoeff‖₊) := mul_le_mul_of_nonneg_left hsep (by norm_num)
      _ = _ := by ring
  have hroot : P.IsRoot (R : ℂ) := by
    change P.eval (R : ℂ) = 0
    rw [show P = Polynomial.ofFn n (fun i => z i - w i) from rfl, ofFn_eq_sum_monomial,
      eval_finsetSum]
    simp only [eval_monomial, sub_mul]
    rw [Finset.sum_sub_distrib]
    have heq : (∑ i : Fin n, z i * (R : ℂ) ^ i.val) =
        ∑ i : Fin n, w i * (R : ℂ) ^ i.val := by simpa only [mul_comm] using hsum
    exact sub_eq_zero.mpr heq
  have hr := (hroot.norm_lt_cauchyBound hP).trans_le hb
  have hnormR : ‖(R : ℂ)‖₊ = (R : ℝ≥0) := by apply NNReal.eq; simp
  rw [hnormR] at hr
  exact (not_lt_of_ge (by exact_mod_cast hR : (2 : ℝ≥0) * ell + 1 ≤ R)) hr

end LeanCanny.CountingHierarchy

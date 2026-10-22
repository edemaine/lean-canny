/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Adapted for lean-canny from TauCeti at revision 034e577c895d28c058d92af4036f7ce0b03081cf.
Source: RingTheory/Polynomial/Subresultant/DegreeDrop/Basic.lean.
Changes: selected algebraic proof slice, project namespace, and pinned Mathlib
compatibility. See STURM_SOURCES.md.
-/
module

public import LeanCanny.Algebra.PrincipalSubresultant.Polynomial
public import LeanCanny.Algebra.PrincipalSubresultant.Corner
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! # Algebraic principal subresultant identities

Adapted proof slice for the signed determinant formula used in Sturm–Tarski queries.
See STURM_SOURCES.md for the upstream source and omitted material.
-/

public section

namespace LeanCanny.Algebra.PrincipalSubresultant

open Polynomial Matrix List

section

open Polynomial

variable {R : Type*}

private theorem lastRow_of_degree_drop [Semiring R] {p q : R[X]} {m n j k : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hjm : j < m) (hjn : j ≤ n)
    (i l : Fin ((m - j) + (n + 1 - j))) (hi : i.val = (m - j) + (n - j)) :
    subresultantCoeffMatrix p q m (n + 1) j k i l =
      if l.val = (m - j) + (n - j) then p.coeff m else 0 := by
  have hi0 : i.val ≠ 0 := by omega
  rw [subresultantCoeffMatrix_apply_eq_coeff hm (hn.trans (Nat.le_succ n))]
  simp only [hi0, ↓reduceIte]
  induction l using Fin.addCases with
  | left l =>
    have hdeg : q.natDegree < i.val + j - l.val := by omega
    have hle : l.val ≤ i.val + j := by omega
    have hne : l.val ≠ (m - j) + (n - j) := by omega
    simp [coeff_X_pow_mul', hle, coeff_eq_zero_of_natDegree_lt hdeg, hne]
  | right l =>
    by_cases h : (m - j) + l.val = (m - j) + (n - j)
    · have hcoeff : i.val + j - l.val = m := by omega
      have hle : l.val ≤ i.val + j := by omega
      simp [coeff_X_pow_mul', h, hcoeff, hle]
    · have hdeg : p.natDegree < i.val + j - l.val := by omega
      have hle : l.val ≤ i.val + j := by omega
      have hne : l.val ≠ n - j := by omega
      simp [coeff_X_pow_mul', hle, hne, coeff_eq_zero_of_natDegree_lt hdeg]

variable [CommRing R]

/-- Lowering an oversized right bound by one scales every coefficient minor by the coefficient
at the left bound. The smaller right terminal index is included, but `j < m` is essential. -/
theorem subresultantCoeff_succ_right {p q : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hjm : j < m) (hjn : j ≤ n)
    (k : ℕ) :
    subresultantCoeff p q m (n + 1) j k =
      p.coeff m * subresultantCoeff p q m n j k := by
  classical
  let d := (m - j) + (n - j)
  have hd : (m - j) + (n + 1 - j) = d + 1 := by dsimp [d]; omega
  let e := finCongr hd
  let M := (subresultantCoeffMatrix p q m (n + 1) j k).reindex e e
  have hlast (l : Fin (d + 1)) :
      M (Fin.last d) l = if l = Fin.last d then p.coeff m else 0 := by
    simpa only [M, Matrix.reindex_apply, Matrix.submatrix_apply, e, finCongr_apply,
      finCongr_symm, Fin.val_cast, Fin.val_last, Fin.ext_iff] using
      lastRow_of_degree_drop hm hn hjm hjn (e.symm (Fin.last d)) (e.symm l) rfl
  -- Removing the last row and column preserves the replaced first row.
  have hminor : M.submatrix Fin.castSucc Fin.castSucc =
      subresultantCoeffMatrix p q m n j k := by
    ext i l
    simp only [Matrix.submatrix_apply, M, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [subresultantCoeffMatrix_apply_eq_coeff hm (hn.trans (Nat.le_succ n)),
      subresultantCoeffMatrix_apply_eq_coeff hm hn]
    induction l using Fin.addCases with
    | left l =>
      have hl : e.symm (Fin.castSucc (Fin.castAdd (n - j) l)) =
          Fin.castAdd (n + 1 - j) l := by ext; rfl
      rw [hl]
      simp [e]
    | right l =>
      have hle : n - j ≤ n + 1 - j := by omega
      have hl : e.symm (Fin.castSucc (Fin.natAdd (m - j) l)) =
          Fin.natAdd (m - j) (Fin.castLE hle l) := by ext; rfl
      rw [hl]
      simp [e]
  have hdet : subresultantCoeff p q m (n + 1) j k = M.det := by
    simp only [M, Matrix.det_reindex_self, subresultantCoeff_def]
  rw [hdet, det_eq_mul_det_submatrix_castSucc_of_row M (by
    intro l hl
    simp [hlast, hl]), hlast, hminor]
  simp [subresultantCoeff_def]

/-- Lowering an oversized right bound scales every coefficient minor by the corresponding
power of the coefficient at the left bound, including the smaller right terminal index. -/
theorem subresultantCoeff_eq_coeff_pow_mul_of_right_degree_drop
    {p q : R[X]} {m n N j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hN : n ≤ N) (hjm : j < m) (hjn : j ≤ n) (k : ℕ) :
    subresultantCoeff p q m N j k =
      p.coeff m ^ (N - n) * subresultantCoeff p q m n j k := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [subresultantCoeff_succ_right hm (hn.trans hN) hjm (hjn.trans hN), ih]
    have hgap : N + 1 - n = (N - n) + 1 := by omega
    rw [hgap, pow_succ]
    ring

/-- Lowering an oversized left bound scales coefficient minors by the right coefficient
power and the column-block sign. The smaller left terminal index is included. -/
theorem subresultantCoeff_eq_sign_mul_coeff_pow_mul_of_left_degree_drop
    {p q : R[X]} {m M n j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hM : m ≤ M) (hjm : j ≤ m) (hjn : j < n) (k : ℕ) :
    subresultantCoeff p q M n j k = (-1) ^ ((M - m) * (n - j)) *
      q.coeff n ^ (M - m) * subresultantCoeff p q m n j k := by
  have hgap : M - j = (M - m) + (m - j) := by omega
  calc
    subresultantCoeff p q M n j k = (-1) ^ ((M - j) * (n - j)) *
        (q.coeff n ^ (M - m) * subresultantCoeff q p n m j k) := by
      rw [subresultantCoeff_comm p q M n j k,
        subresultantCoeff_eq_coeff_pow_mul_of_right_degree_drop hn hm hM hjn hjm]
    _ = _ := by
      rw [subresultantCoeff_comm p q m n j k, hgap, add_mul, pow_add]
      ring

/-- Lowering an oversized right degree bound by one multiplies the principal
subresultant by the coefficient at the left bound. The terminal smaller index is included. -/
theorem psc_succ_right {p q : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hjm : j ≤ m) (hjn : j ≤ n) :
    psc p q m (n + 1) j = p.coeff m * psc p q m n j := by
  by_cases hjm' : j < m
  · simpa only [subresultantCoeff_self] using
      subresultantCoeff_succ_right hm hn hjm' hjn j
  · have hjeq : j = m := by omega
    subst j
    rw [psc_left_bound, psc_left_bound]
    have hgap : n + 1 - m = (n - m) + 1 := by omega
    rw [hgap, pow_succ, mul_comm]

/-- An arbitrary drop in the right bound contributes the corresponding power of the
coefficient at the left bound. The lower right bound need only dominate the degree. -/
theorem psc_eq_coeff_pow_mul_of_right_degree_drop {p q : R[X]}
    {m n N j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hN : n ≤ N) (hjm : j ≤ m) (hjn : j ≤ n) :
    psc p q m N j = p.coeff m ^ (N - n) * psc p q m n j := by
  by_cases hjm' : j < m
  · simpa only [subresultantCoeff_self] using
      subresultantCoeff_eq_coeff_pow_mul_of_right_degree_drop hm hn hN hjm' hjn j
  · have hjeq : j = m := by omega
    subst j
    rw [psc_left_bound, psc_left_bound, ← pow_add]
    congr 1
    omega

/-- Dropping the left bound also contributes the sign of moving its removed columns
past the right block. The lower left bound need only dominate the degree. -/
theorem psc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop {p q : R[X]}
    {m M n j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hM : m ≤ M) (hjm : j ≤ m) (hjn : j ≤ n) :
    psc p q M n j =
      (-1) ^ ((M - m) * (n - j)) * q.coeff n ^ (M - m) * psc p q m n j := by
  by_cases hjn' : j < n
  · simpa only [subresultantCoeff_self] using
      subresultantCoeff_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hm hn hM hjm hjn' j
  · have hjeq : j = n := by omega
    subst j
    simp only [psc_right_bound, Nat.sub_self, mul_zero, pow_zero, one_mul, ← pow_add]
    congr 1
    omega

/-- At strict subresultant indices, simultaneous drops in both degree bounds force
vanishing. Terminal indices are excluded: their empty determinant can still be `1`. -/
theorem psc_eq_zero_of_natDegree_lt_bounds {p q : R[X]} {m n j : ℕ}
    (hm : p.natDegree < m) (hn : q.natDegree < n) (hj : j < min m n) :
    psc p q m n j = 0 := by
  have hnpos : 0 < n := by omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  rw [psc_succ_right hm.le (by omega) (by omega) (by omega),
    coeff_eq_zero_of_natDegree_lt hm, zero_mul]

end

end LeanCanny.Algebra.PrincipalSubresultant

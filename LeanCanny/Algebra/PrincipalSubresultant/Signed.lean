/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Adapted for lean-canny from TauCeti at revision 034e577c895d28c058d92af4036f7ce0b03081cf.
Source: RingTheory/Polynomial/Subresultant/Signed.lean.
Changes: selected algebraic proof slice, project namespace, and pinned Mathlib
compatibility. See STURM_SOURCES.md.
-/
module

public import LeanCanny.Algebra.PrincipalSubresultant.DegreeDrop
public import LeanCanny.Algebra.PrincipalSubresultant.Choose
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

variable {R S : Type*} [CommRing R]

/-- Signed principal subresultant coefficients at fixed bounds. Inside the
subresultant range they are signed Sylvester minors. Above that range the
coefficients at the two input bounds are retained, and all other entries vanish.
The equal-bound terminal entry is `1`, including for zero inputs. -/
noncomputable def signedPsc (p q : R[X]) (m n j : ℕ) : R :=
  if j ≤ min m n then (-1) ^ (m - j).choose 2 * psc p q m n j
  else if j = m then p.coeff m
  else if j = n then q.coeff n
  else 0

/-- Conversion from the Sylvester convention to the signed Sylvester–Habicht
normalization. The last exponent accounts for swapping the column blocks. -/
theorem signedPsc_def (p q : R[X]) (m n j : ℕ) :
    signedPsc p q m n j =
      if j ≤ min m n then
        (-1) ^ ((m + n - 2 * j).choose 2 + (n - j).choose 2 +
          (m - j) * (n - j)) * psc p q m n j
      else if j = m then p.coeff m
      else if j = n then q.coeff n
      else 0 := by
  by_cases hj : j ≤ min m n
  · have hsize : m + n - 2 * j = (m - j) + (n - j) := by omega
    have hexp : (m + n - 2 * j).choose 2 + (n - j).choose 2 +
        (m - j) * (n - j) =
        (m - j).choose 2 + 2 * ((n - j).choose 2 + (m - j) * (n - j)) := by
      rw [hsize, add_choose_two]
      omega
    simp [signedPsc, hj, hexp, pow_add, pow_mul]
  · simp [signedPsc, hj]

/-- Within the subresultant range only the left-bound gap determines the sign. -/
@[simp]
theorem signedPsc_of_le (p q : R[X]) {m n j : ℕ}
    (hj : j ≤ min m n) :
    signedPsc p q m n j = (-1) ^ (m - j).choose 2 * psc p q m n j := by
  simp [signedPsc, hj]

/-- Above the smaller bound only the two input-bound coefficients are retained. -/
@[simp]
theorem signedPsc_of_lt (p q : R[X]) {m n j : ℕ}
    (hj : min m n < j) :
    signedPsc p q m n j =
      if j = m then p.coeff m else if j = n then q.coeff n else 0 := by
  simp [signedPsc, hj.not_ge]

/-- Coefficients beyond both formal bounds vanish. -/
@[simp]
theorem signedPsc_eq_zero_of_max_lt (p q : R[X]) {m n j : ℕ}
    (hj : max m n < j) : signedPsc p q m n j = 0 := by
  have hle : ¬ j ≤ min m n := by omega
  have hm : j ≠ m := by omega
  have hn : j ≠ n := by omega
  simp [signedPsc, hle, hm, hn]

/-- Signed coefficients specialize at fixed bounds, even when degrees drop. -/
@[simp]
theorem signedPsc_map_map [CommRing S] (f : R →+* S)
    (p q : R[X]) (m n j : ℕ) :
    signedPsc (p.map f) (q.map f) m n j = f (signedPsc p q m n j) := by
  simp [signedPsc, apply_ite f]

/-- The smaller left bound has no sign correction; a larger left bound retains
the left input coefficient itself. -/
@[simp]
theorem signedPsc_left_bound (p q : R[X]) (m n : ℕ) :
    signedPsc p q m n m =
      if m ≤ n then p.coeff m ^ (n - m) else p.coeff m := by
  by_cases hmn : m ≤ n <;> simp [signedPsc, hmn]

/-- The smaller right bound retains the gap sign and the terminal power; a larger
right bound retains the right input coefficient itself. -/
@[simp]
theorem signedPsc_right_bound (p q : R[X]) (m n : ℕ) :
    signedPsc p q m n n =
      if n ≤ m then (-1) ^ (m - n).choose 2 * q.coeff n ^ (m - n)
      else q.coeff n := by
  by_cases hnm : n ≤ m
  · simp [signedPsc, hnm]
  · have hne : n ≠ m := by omega
    simp [signedPsc, hnm, hne]

/-- Swapping inputs changes both the normalization and the column-block order. -/
theorem signedPsc_comm (p q : R[X]) {m n j : ℕ}
    (hj : j ≤ min m n) :
    signedPsc p q m n j =
      (-1) ^ ((m - j).choose 2 + (n - j).choose 2 + (m - j) * (n - j)) *
        signedPsc q p n m j := by
  rw [signedPsc_of_le p q hj, signedPsc_of_le q p (by omega), psc_comm]
  simp only [pow_add]
  rcases neg_one_pow_eq_or R ((n - j).choose 2) with h | h <;> rw [h] <;> ring

/-- Scaling the left input scales its signed minor by the number of its columns. -/
theorem signedPsc_C_mul_left (p q : R[X]) (r : R) {m n j : ℕ}
    (hj : j ≤ min m n) :
    signedPsc (C r * p) q m n j = r ^ (n - j) * signedPsc p q m n j := by
  simp only [signedPsc_of_le _ _ hj, psc_C_mul_left]
  ring

/-- Scaling the right input scales its signed minor by the number of its columns. -/
theorem signedPsc_C_mul_right (p q : R[X]) (r : R) {m n j : ℕ}
    (hj : j ≤ min m n) :
    signedPsc p (C r * q) m n j = r ^ (m - j) * signedPsc p q m n j := by
  simp only [signedPsc_of_le _ _ hj, psc_C_mul_right]
  ring

/-- A zero left input makes an in-range signed minor vanish when its column
block is nonempty. This excludes the empty-determinant terminal case.
Not a simp lemma: `signedPsc_of_le` already rewrites its left-hand side. -/
theorem signedPsc_zero_left (q : R[X]) {m n j : ℕ}
    (hj : j ≤ min m n) (hjn : j < n) : signedPsc 0 q m n j = 0 := by
  have h := signedPsc_C_mul_left (0 : R[X]) q 0 hj
  simpa [zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hjn))] using h

/-- A zero right input makes an in-range signed minor vanish when its column
block is nonempty. This excludes the empty-determinant terminal case.
Not a simp lemma: `signedPsc_of_le` already rewrites its left-hand side. -/
theorem signedPsc_zero_right (p : R[X]) {m n j : ℕ}
    (hj : j ≤ min m n) (hjm : j < m) : signedPsc p 0 m n j = 0 := by
  have h := signedPsc_C_mul_right p (0 : R[X]) 0 hj
  simpa [zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hjm))] using h

/-- Lowering the right bound contributes a leading-coefficient power, with no
additional sign. The smaller terminal index is included. -/
theorem signedPsc_eq_coeff_pow_mul_of_right_degree_drop
    {p q : R[X]} {m n N j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hN : n ≤ N) (hjm : j ≤ m) (hjn : j ≤ n) :
    signedPsc p q m N j = p.coeff m ^ (N - n) * signedPsc p q m n j := by
  rw [signedPsc_of_le p q (by omega), signedPsc_of_le p q (by omega),
    psc_eq_coeff_pow_mul_of_right_degree_drop hm hn hN hjm hjn]
  ring

/-- Lowering the left bound contributes the normalization-gap sign as well as
the power of the coefficient at the right bound. Terminal indices are included. -/
theorem signedPsc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop
    {p q : R[X]} {m M n j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hM : m ≤ M) (hjm : j ≤ m) (hjn : j ≤ n) :
    signedPsc p q M n j =
      (-1) ^ ((M - m).choose 2 + (M - m) * (m + n - 2 * j)) *
        q.coeff n ^ (M - m) * signedPsc p q m n j := by
  have hgap : M - j = (M - m) + (m - j) := by omega
  have hsize : m + n - 2 * j = (m - j) + (n - j) := by omega
  rw [signedPsc_of_le p q (by omega), signedPsc_of_le p q (by omega),
    psc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hm hn hM hjm hjn,
    hgap, add_choose_two, hsize]
  simp only [mul_add, pow_add]
  ring

/-- Simultaneous strict degree drops make every strict-index signed minor zero.
The equal-bound terminal determinant is deliberately excluded. -/
theorem signedPsc_eq_zero_of_natDegree_lt_bounds {p q : R[X]}
    {m n j : ℕ} (hm : p.natDegree < m) (hn : q.natDegree < n)
    (hj : j < min m n) : signedPsc p q m n j = 0 := by
  rw [signedPsc_of_le p q hj.le, psc_eq_zero_of_natDegree_lt_bounds hm hn hj, mul_zero]

end

end LeanCanny.Algebra.PrincipalSubresultant

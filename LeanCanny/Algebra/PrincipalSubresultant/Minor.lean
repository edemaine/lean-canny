/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalSubresultant.Signed
public import LeanCanny.Algebra.SubresultantBounds

/-! # Principal coefficients use the existing Sylvester-minor convention

The equalities include terminal and out-of-range indices at the matrix level.
Only the polynomial-coefficient identification needs an interior-order hypothesis.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrincipalSubresultant
open Polynomial

variable {R : Type*} [CommRing R]

/-- The determinant matrix agrees with the already streamed principal minor. -/
theorem matrix_eq_minor (p q : R[X]) (m n k : ℕ) :
    subresultantMatrix p q m n k = Subresultant.minor p q m n k k := by
  funext i j
  have hr : Subresultant.rowIndex k k i.val = i.val + k := by
    by_cases hi : i.val = 0 <;> simp [Subresultant.rowIndex, hi, Nat.add_comm]
  induction j using Fin.addCases <;>
    simp only [subresultantMatrix_castAdd, subresultantMatrix_natAdd,
      Subresultant.minor, Matrix.of_apply,
      Fin.addCases_left, Fin.addCases_right, Subresultant.band, hr]

/-- Every principal coefficient, including the terminal case, is the selected determinant. -/
theorem psc_eq_minor (p q : R[X]) (m n k : ℕ) :
    psc p q m n k = (Subresultant.minor p q m n k k).det := by
  rw [psc_def, matrix_eq_minor]

/-- Interior principal coefficients are the top coefficients of existing subresultants. -/
theorem psc_eq_coeff (p q : R[X]) (m n k : ℕ) (hm : k < m) (hn : k < n) :
    psc p q m n k = (Subresultant.polynomial p q m n k).coeff k := by
  rw [psc_eq_minor, Subresultant.coeff]
  simp [hm, hn]

/-- The signed normalization needs only a known sign times the same determinant. -/
theorem signedPsc_eq_minor (p q : R[X]) (m n k : ℕ) (hk : k ≤ min m n) :
    signedPsc p q m n k =
      (-1) ^ (m - k).choose 2 * (Subresultant.minor p q m n k k).det := by
  rw [signedPsc_of_le p q hk, psc_eq_minor]

/-- Signed normalization preserves the existing integer determinant bit budget.
The terminal principal index is included. -/
theorem signedPsc_size_le (p q : ℤ[X]) (m n k bp bq : ℕ) (hk : k ≤ min m n)
    (hp : ∀ i, (p.coeff i).natAbs ≤ 2 ^ bp)
    (hq : ∀ i, (q.coeff i).natAbs ≤ 2 ^ bq) :
    (signedPsc p q m n k).natAbs.size ≤ Subresultant.budget m n k bp bq := by
  rw [signedPsc_eq_minor p q m n k hk]
  simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
    one_pow, one_mul] using Subresultant.minor_det_size_le p q m n k k bp bq hp hq

end LeanCanny.Algebra.PrincipalSubresultant

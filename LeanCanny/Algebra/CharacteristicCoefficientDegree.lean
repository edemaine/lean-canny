/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCharacteristic
public import LeanCanny.Algebra.PolynomialKronecker

/-! # Parameter-degree bounds for characteristic coefficients

Uniform degree bounds for polynomial matrix entries bound the parameter
degree of every characteristic coefficient. Swapping the two polynomial
variables reduces the assertion to the determinant degree bound.
-/

@[expose] public section

namespace LeanCanny.Algebra.AffineCharacteristic
open scoped BigOperators Classical
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem subtractiveMatrix_coefficient_degree (A : Matrix ι ι (Polynomial R)) (E : ℕ)
    (hA : ∀ r s, (A r s).natDegree ≤ E) (r s : ι) (j : ℕ) :
    (((subtractiveMatrix A r s).coeff j).natDegree) ≤ E := by
  cases j with
  | zero => simpa [subtractiveMatrix] using hA r s
  | succ j =>
    cases j with
    | zero =>
      by_cases hrs : r = s <;> simp [subtractiveMatrix, Matrix.one_apply, hrs]
    | succ j => simp [subtractiveMatrix]

theorem subtractive_det_coefficient_degree (A : Matrix ι ι (Polynomial R)) (E : ℕ)
    (hA : ∀ r s, (A r s).natDegree ≤ E) (j : ℕ) :
    ((subtractiveMatrix A).det.coeff j).natDegree ≤ Fintype.card ι * E := by
  have h := PolynomialKronecker.determinant_inner_degree (subtractiveMatrix A) (fun _ => E)
    (subtractiveMatrix_coefficient_degree A E hA) j
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using h

end LeanCanny.Algebra.AffineCharacteristic

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzTransform

/-!
# The determinant as an entry of a transformation product

The coefficient transformations of successive trailing principal matrices act
on the constant polynomial 1. Their ordered product contains every
characteristic coefficient in its first column. The determinant is its signed
top-left entry. Padding gives square matrices of one common width, enabling
balanced multiplication without storing the intermediate coefficient vectors.
This file specifies the factors as a list; an encoded evaluator must supply
uniform factor access without materializing that list.
-/

@[expose] public section

noncomputable section

namespace LeanCanny.Algebra.Berkowitz
open Matrix Polynomial

variable {R : Type*} [CommRing R]

def factors (w : ℕ) : {n : ℕ} → Matrix (Fin n) (Fin n) R → List (Matrix (Fin w) (Fin w) R)
  | 0, _ => []
  | _ + 1, A => transformation w A :: factors w (A.submatrix Fin.succ Fin.succ)

theorem factors_length {n : ℕ} (w : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    (factors w A).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [factors, ih]

theorem factors_prod_mulVec {n w : ℕ} (A : Matrix (Fin n) (Fin n) R) (hn : n ≤ w) :
    (factors w A).prod *ᵥ (fun i : Fin w => if i.val = 0 then 1 else 0) =
      coefficientVector w A := by
  induction n with
  | zero =>
      funext i
      simp [factors, coefficientVector, coeff_one]
  | succ n ih =>
      rw [factors, List.prod_cons, ← Matrix.mulVec_mulVec, ih _ (by omega)]
      exact transformation_mulVec A (by omega)

theorem factors_prod_entry {n w : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hn : n ≤ w) (hw : 0 < w) (d : Fin w) :
    (factors w A).prod d ⟨0, hw⟩ = A.charpoly.coeff d.val := by
  have h := congrArg (fun v : Fin w → R => v d) (factors_prod_mulVec A hn)
  have heq (i : Fin w) : i.val = 0 ↔ i = ⟨0, hw⟩ := by simp [Fin.ext_iff]
  simpa [Matrix.mulVec, dotProduct, heq, coefficientVector] using h

theorem det_eq_factors_prod_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    A.det = (-1) ^ n * (factors (n + 1) A).prod 0 0 := by
  have h := factors_prod_entry (w := n + 1) A (by omega) (by omega) (0 : Fin (n + 1))
  calc
    A.det = (-1) ^ n * A.charpoly.coeff 0 := by
      simpa only [Fintype.card_fin] using Matrix.det_eq_sign_charpoly_coeff A
    _ = (-1) ^ n * (factors (n + 1) A).prod 0 0 := congrArg ((-1 : R) ^ n * ·) h.symm

end LeanCanny.Algebra.Berkowitz

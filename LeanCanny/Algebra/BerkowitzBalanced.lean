/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzProduct
public import LeanCanny.Algebra.MatrixProductEntry

/-!
# Balanced evaluation of characteristic coefficients

A factor accessor follows trailing principal blocks and returns only the
requested coefficient transformation. Balanced interval recursion then
computes a characteristic coefficient, and hence the determinant, at height
`n.size`. The accessor does not construct the full factor list.

This proves algebraic correctness and the recursion-height requirement. Finite
sum streaming, binary access to trailing blocks and scalar power moments,
and a complete workspace certificate remain to be implemented. In particular,
no complexity bound for the recursive factor accessor is asserted here.
-/

@[expose] public section

noncomputable section

namespace LeanCanny.Algebra.Berkowitz
open Matrix

variable {R : Type*} [CommRing R]

def factorAt (w : ℕ) : {n : ℕ} → Matrix (Fin n) (Fin n) R → ℕ → Matrix (Fin w) (Fin w) R
  | 0, _, _ => 1
  | _ + 1, A, 0 => transformation w A
  | _ + 1, A, s + 1 => factorAt w (A.submatrix Fin.succ Fin.succ) s

theorem factors_getD {n : ℕ} (w : ℕ) (A : Matrix (Fin n) (Fin n) R) (s : ℕ) :
    (factors w A)[s]?.getD 1 = factorAt w A s := by
  induction n generalizing s with
  | zero => simp [factors, factorAt]
  | succ n ih => cases s <;> simp [factors, factorAt, ih]

theorem factor_product_eq {n : ℕ} (w : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    MatrixProduct.product (factorAt w A) 0 n = (factors w A).prod := by
  have h := MatrixProduct.product_getD (factors w A)
  simpa only [factors_length, factors_getD] using h

theorem balanced_entry_eq_coeff {n w : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hn : n ≤ w) (hw : 0 < w) (d : Fin w) :
    MatrixProduct.entry (factorAt w A) n.size 0 n d ⟨0, hw⟩ = A.charpoly.coeff d.val := by
  rw [MatrixProduct.entry_size_eq_product, factor_product_eq]
  exact factors_prod_entry A hn hw d

def balancedCoefficient {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (d : Fin (n + 1)) : R :=
  MatrixProduct.entry (factorAt (n + 1) A) n.size 0 n d 0

theorem balancedCoefficient_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (d : Fin (n + 1)) :
    balancedCoefficient A d = A.charpoly.coeff d.val :=
  balanced_entry_eq_coeff A (by omega) (by omega) d

def balancedDeterminant {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : R :=
  (-1) ^ n * balancedCoefficient A 0

theorem balancedDeterminant_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    balancedDeterminant A = A.det := by
  rw [balancedDeterminant, balancedCoefficient_eq, Matrix.det_eq_sign_charpoly_coeff]
  simp only [Fintype.card_fin, Fin.val_zero]

end LeanCanny.Algebra.Berkowitz

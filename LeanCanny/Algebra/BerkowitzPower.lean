/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzBalanced
public import LeanCanny.Algebra.LayeredMatrixMachine
public import LeanCanny.Algebra.MatrixPowerHalting

/-!
# Determinants through the existing streamed power machine

The layered coefficient-transform matrix has dimension `(n+1)^2`. Its nth
power contains the characteristic coefficients. The existing continuation
machine and bitstring controller therefore evaluate them, and zero testing
of the constant coefficient tests the determinant.

The stored power states over residues have an explicit quadratic bound in
the binary lengths of n and the modulus. This excludes the workspace for
accessing layered entries: those entries still involve scalar power moments.
The abstract clock similarly counts entry access as one operation. The later
`BerkowitzPSPACE` module incorporates a uniform encoded factor evaluator and its
workspace to prove modular determinant zero testing in PSPACE.
-/

@[expose] public section

noncomputable section

namespace LeanCanny.Algebra.Berkowitz
open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

def powerMatrix (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin ((n + 1) * (n + 1))) (Fin ((n + 1) * (n + 1))) R :=
  MatrixProduct.layeredFin (factorAt (n + 1) A) (n + 1)

def powerQuery (n : ℕ) (d : Fin (n + 1)) : MatrixPower.Query ((n + 1) * (n + 1)) where
  height := n.size
  exponent := n
  row := finProdFinEquiv ((0 : Fin (n + 1)), d)
  col := finProdFinEquiv (Fin.last n, (0 : Fin (n + 1)))

theorem powerMatrix_pow (A : Matrix (Fin n) (Fin n) R) (d : Fin (n + 1)) :
    (powerMatrix A ^ n) (powerQuery n d).row (powerQuery n d).col = A.charpoly.coeff d.val := by
  unfold powerMatrix powerQuery
  rw [MatrixProduct.layeredFin_pow_apply]
  simp only [Fin.val_zero, Nat.zero_add, Fin.val_last, ↓reduceIte]
  rw [factor_product_eq]
  exact factors_prod_entry A (by omega) (by omega) d

theorem det_eq_powerMatrix (A : Matrix (Fin n) (Fin n) R) :
    A.det = (-1) ^ n * (powerMatrix A ^ n) (powerQuery n 0).row (powerQuery n 0).col := by
  rw [powerMatrix_pow, Matrix.det_eq_sign_charpoly_coeff]
  simp only [Fintype.card_fin, Fin.val_zero]

theorem powerMatrix_zero_iff (A : Matrix (Fin n) (Fin n) R) :
    (powerMatrix A ^ n) (powerQuery n 0).row (powerQuery n 0).col = 0 ↔ A.det = 0 := by
  rw [det_eq_powerMatrix]
  simp only [neg_one_pow_mul_eq_zero_iff]

theorem run_powerMatrix (A : Matrix (Fin n) (Fin n) R) (d : Fin (n + 1)) :
    (MatrixPower.step (powerMatrix A))^[MatrixPower.work ((n + 1) * (n + 1)) n.size n + 1]
      (.eval (powerQuery n d) []) = .done (A.charpoly.coeff d.val) := by
  rw [show powerQuery n d = ⟨n.size, n, (powerQuery n d).row, (powerQuery n d).col⟩ from rfl,
    MatrixPower.run_pow, powerMatrix_pow]

theorem power_dimension_size (n : ℕ) : ((n + 1) * (n + 1)).size ≤ 2 * n.size + 1 := by
  have hn := Nat.lt_size_self n
  have hprod : (n + 1) * (n + 1) ≤ 2 ^ n.size * 2 ^ n.size := Nat.mul_le_mul (by omega) (by omega)
  have hsize := Nat.size_le_size hprod
  rw [← pow_add, Nat.size_pow] at hsize
  omega

theorem power_work_bound (n : ℕ) :
    MatrixPower.work ((n + 1) * (n + 1)) n.size n + 1 ≤
      2 ^ ((2 * n.size + 3) * n.size + 1) := by
  have hd := power_dimension_size n
  have he : (((n + 1) * (n + 1)).size + 2) * n.size + 1 ≤
      (2 * n.size + 3) * n.size + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right n.size (by omega)) 1
  exact (MatrixPower.work_add_one_le_two_pow _ _ _).trans (Nat.pow_le_pow_right (by decide) he)

theorem run_powerMatrix_residue_length (m : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (d : Fin (n + 1)) (t : ℕ) :
    (MatrixPower.stateBits MatrixPower.residueBits
      ((MatrixPower.step (powerMatrix A))^[t] (.eval (powerQuery n d) []))).length ≤
        64 * (3 * n.size + m.size + 2) ^ 2 := by
  have h := MatrixPower.run_residueBits_quadratic m (powerMatrix A) n t
    (powerQuery n d).row (powerQuery n d).col
  have hd := power_dimension_size n
  have hb : ((n + 1) * (n + 1)).size + n.size + m.size + 1 ≤ 3 * n.size + m.size + 2 := by omega
  exact h.trans (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hb 2))

theorem controller_residue_length (ops : MatrixPower.Controller.Callbacks) (c : List Bool)
    (m : ℕ) [NeZero m] (A : Matrix (Fin n) (Fin n) (ZMod m))
    (hc : MatrixPower.Controller.CorrectAt ops c (powerMatrix A) MatrixPower.residueBits)
    (d : Fin (n + 1)) (t : ℕ) :
    ((MatrixPower.Controller.step ops)^[t]
      (Complexity.pair c (MatrixPower.stateBits (MatrixPower.residueBits (m := m))
        (.eval (powerQuery n d) [])))).length ≤
          2 * c.length + 2 + 64 * (3 * n.size + m.size + 2) ^ 2 := by
  rw [MatrixPower.Controller.iterate_packet ops c _ MatrixPower.residueBits hc,
    Complexity.pair_length]
  exact Nat.add_le_add_left (run_powerMatrix_residue_length m A d t) _

theorem controller_zero_iff (ops : MatrixPower.Controller.Callbacks) (c : List Bool)
    (m : ℕ) [NeZero m] (A : Matrix (Fin n) (Fin n) (ZMod m))
    (hc : MatrixPower.Controller.CorrectAt ops c (powerMatrix A) MatrixPower.residueBits) :
    MatrixPower.Controller.zeroAnswer
      ((MatrixPower.Controller.step ops)^[MatrixPower.work ((n + 1) * (n + 1)) n.size n + 1]
        (Complexity.pair c (MatrixPower.stateBits (MatrixPower.residueBits (m := m))
          (.eval (powerQuery n 0) [])))) = true ↔ A.det = 0 := by
  rw [MatrixPower.Controller.iterate_packet ops c _ MatrixPower.residueBits hc,
    run_powerMatrix, MatrixPower.Controller.zeroAnswer_done]
  rw [Matrix.det_eq_sign_charpoly_coeff, neg_one_pow_mul_eq_zero_iff]
  simp only [Fin.val_zero]

end LeanCanny.Algebra.Berkowitz

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalParameterMass
public import LeanCanny.Algebra.LinearCoefficientBounds
public import LeanCanny.Computation.PolyTimeBinaryNat
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! # Uniform binary bit budgets for integer characteristic coefficients -/

@[expose] public section
namespace LeanCanny.Algebra.CharacteristicIntegerBounds
open Polynomial
open scoped Classical

def budget (N B : ℕ) : ℕ := N.size * N + N * (B + 1) + 1

theorem budget_binary {N B : List Bool → ℕ} (hN : BinaryFn N) (hB : BinaryFn B) :
    BinaryFn (fun c => budget (N c) (B c)) :=
  ((hN.size.mul hN).add (hN.mul (hB.add (BinaryFn.const 1)))).add (BinaryFn.const 1)

theorem coefficient_bits {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ B) (k : ℕ) :
    (A.charpoly.coeff k).natAbs.size ≤ budget n B := by
  have hp : 1 + 2 ^ B ≤ 2 ^ (B + 1) := by
    have := Nat.one_le_two_pow (n := B)
    rw [pow_succ]
    omega
  have hx : coefficientMass (X : ℤ[X]) = 1 := by simpa only [pow_one] using coefficientMass_X_pow 1
  have hc (i j : Fin n) : coefficientMass (Matrix.charmatrix A i j) ≤ 2 ^ (B + 1) := by
    by_cases hij : i = j
    · subst j
      rw [Matrix.charmatrix_apply_eq]
      exact (coefficientMass_sub_le _ _).trans (by
        rw [hx, coefficientMass_C]
        exact (Nat.add_le_add_left (hA i i) 1).trans hp)
    · rw [Matrix.charmatrix_apply_ne _ _ _ hij, coefficientMass_neg, coefficientMass_C]
      exact (hA i j).trans ((Nat.le_add_left _ _).trans hp)
  have hd := det_coefficientMass_le_pow (Matrix.charmatrix A) (B + 1) hc
  have he := (coeff_natAbs_le_coefficientMass (Matrix.charmatrix A).det k).trans hd
  have hs := Nat.size_le_size he
  simpa only [Matrix.charpoly, Fintype.card_fin, Nat.size_pow, budget] using hs

end LeanCanny.Algebra.CharacteristicIntegerBounds

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FrozenAffineCopies
public import LeanCanny.Algebra.MvCoefficientMass

/-! # Coefficient-mass bounds for frozen affine copies and midpoint tests -/

@[expose] public section
namespace LeanCanny.Algebra.FrozenAffineCopies
open MvPolynomial
open scoped Classical
set_option maxHeartbeats 300000
variable {n m : ℕ}

theorem row_mass (p : Fin n → MvPolynomial (Fin n) ℤ) (h : Fin n) (frozen : Fin m → Bool)
    (k : Fin m) (i : Fin n) : MvMass.mass (row p h frozen k i) ≤ MvMass.mass (p i) + 1 := by
  apply (MvMass.sub_le _ _).trans
  apply Nat.add_le_add (MvMass.rename_le _ _)
  split_ifs
  · simp
  · simp

theorem system_mass (p : Fin n → MvPolynomial (Fin n) ℤ) (E : Polynomial ℤ) (h : Fin n)
    (frozen : Fin m → Bool) (bP bE : ℕ) (hp : ∀ i, MvMass.mass (p i) ≤ 2 ^ bP)
    (hE : coefficientMass E ≤ 2 ^ bE) (j : Fin (m * n + 1)) :
    MvMass.mass (system p E h frozen j) ≤ 2 ^ (bP + bE + 1) := by
  refine Fin.cases ?_ (fun r => ?_) j
  · apply (RetainedParameterPolynomial.mass E).trans
    exact hE.trans (Nat.pow_le_pow_right (by decide) (by omega))
  · apply (row_mass p h frozen _ _).trans
    calc
      _ ≤ 2 ^ bP + 1 := Nat.add_le_add_right (hp _) 1
      _ ≤ 2 ^ (bP + 1) := by
        have H := Nat.one_le_pow bP 2 (by decide)
        rw [pow_succ]
        omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

theorem midpoint_mass (i : Fin n) : MvMass.mass (midpoint i) ≤ 4 := by
  apply (MvMass.sub_le _ _).trans
  apply (Nat.add_le_add_right (MvMass.sub_le _ _) _).trans
  apply (Nat.add_le_add_right (Nat.add_le_add_right (MvMass.mul_le _ _) _) _).trans
  simp only [MvMass.X, MvMass.C]
  norm_num

end LeanCanny.Algebra.FrozenAffineCopies

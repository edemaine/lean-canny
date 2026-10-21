/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ScaledSquarefreeBounds
public import LeanCanny.Algebra.UniformPrimitivePairBounds

/-! # Common source bounds for integer square-free preprocessing -/

@[expose] public section

namespace LeanCanny.Algebra.SeparableBits
open Polynomial

theorem gcdBudget_uniform (F : Family) (c : List Bool) (T : ℕ) (hT : 4 ≤ T)
    (hm : (F.polynomial c).natDegree ≤ T) (hb : F.height c ≤ T) : gcdBudget F c ≤ T ^ 4 := by
  have hd : (F.polynomial c).natDegree + ((F.polynomial c).natDegree - 1) ≤ T + T := by omega
  have hc : F.height c + (F.polynomial c).natDegree.size ≤ T + T :=
    Nat.add_le_add hb ((Nat.size_le_self _).trans hm)
  have hr : gcdBudget F c ≤ 8 * T ^ 2 + 1 := by
    change _ + _ + 1 ≤ _
    calc
      _ ≤ (T + T) * (T + T) + (T + T) * (T + T) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul ((Nat.size_le_self _).trans hd) hd)
          (Nat.mul_le_mul hd hc)) 1
      _ = _ := by ring
  have h0 : 1 ≤ T ^ 2 := Nat.one_le_pow _ _ (by omega)
  exact (hr.trans (by omega : 8 * T ^ 2 + 1 ≤ 16 * T ^ 2)).trans (CannyResultantBits.sixteen_mul_pow_le T 2 hT)

theorem squarefreeBudget_uniform (F : Family) (c : List Bool) (T : ℕ) (hT : 4 ≤ T)
    (hm : (F.polynomial c).natDegree ≤ T) (hb : F.height c ≤ T) : squarefreeBudget F c ≤ T ^ 7 := by
  have hg := gcdBudget_uniform F c T hT hm hb
  have hN : (F.polynomial c).natDegree + 1 ≤ T + T := by omega
  have hr : squarefreeBudget F c ≤ 2 * T ^ 5 + 6 * T ^ 2 + 1 := by
    unfold squarefreeBudget
    calc
      _ ≤ (T + T) * (T + T) + (T + T) * (T ^ 4 + T) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul ((Nat.size_le_self _).trans hN) hN)
          (Nat.mul_le_mul hN (Nat.add_le_add hg hb))) 1
      _ = _ := by ring
  have h2 : T ^ 2 ≤ T ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h0 : 1 ≤ T ^ 5 := Nat.one_le_pow _ _ (by omega)
  exact (hr.trans (by omega : 2 * T ^ 5 + 6 * T ^ 2 + 1 ≤ 16 * T ^ 5)).trans (CannyResultantBits.sixteen_mul_pow_le T 5 hT)

theorem squarefree_mass_uniform (F : Family) (c : List Bool) (T : ℕ) (hT : 4 ≤ T)
    (hm : (F.polynomial c).natDegree ≤ T) (hb : F.height c ≤ T) (hne : F.polynomial c ≠ 0) :
    coefficientMass (ScaledSquarefree.polynomial (F.polynomial c)) ≤ 2 ^ (T ^ 16) := by
  have hc (k : ℕ) : ((ScaledSquarefree.polynomial (F.polynomial c)).coeff k).natAbs ≤ 2 ^ (T ^ 7) :=
    (Nat.size_le.mp ((squarefree_coefficient_size F c k).trans (squarefreeBudget_uniform F c T hT hm hb))).le
  have hd := (ScaledSquarefree.polynomial_natDegree_le (F.polynomial c) hne).trans hm
  have hmass := coefficientMass_le_pow_of_degree_coeff _ T (T ^ 7) hd hc
  have hs := Nat.size_le_self (T + 1)
  have h1 : T ≤ T ^ 7 := by simpa using Nat.pow_le_pow_right (n := T) (by omega) (show 1 ≤ 7 by decide)
  have h0 : 1 ≤ T ^ 7 := Nat.one_le_pow _ _ (by omega)
  have h9 : 16 * T ^ 7 ≤ T ^ 9 := CannyResultantBits.sixteen_mul_pow_le T 7 hT
  have h16 : T ^ 9 ≤ T ^ 16 := Nat.pow_le_pow_right (by omega) (by decide)
  exact hmass.trans (Nat.pow_le_pow_right (by decide) (show T ^ 7 + (T + 1).size ≤ T ^ 16 by omega))

end LeanCanny.Algebra.SeparableBits

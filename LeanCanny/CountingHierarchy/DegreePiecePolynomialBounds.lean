/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.DegreePiecePolynomial

/-! # A uniform degree bound for every closed degree-piece lift -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial LeanCanny.Algebra
open scoped BigOperators Classical

variable {n : ℕ}

theorem liftedFirstCoefficient_degree_le (P : MvPolynomial (Fin (n + 1)) ℤ) (j : ℕ) :
    (liftedFirstCoefficient P j).totalDegree ≤ P.totalDegree :=
  (MvPolynomial.totalDegree_rename_le _ _).trans (firstVariableCoefficient_degree_le P j)

theorem degreePiecePolynomial_degree_le (P : MvPolynomial (Fin (n + 1)) ℤ) (N d : ℕ) :
    (degreePiecePolynomial P N d).totalDegree ≤ 2 * (P.totalDegree + 1) := by
  rw [degreePiecePolynomial]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_pow _ _).trans
    apply Nat.mul_le_mul_left 2
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le _ (by simp)
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      rw [MvPolynomial.totalDegree_X]
      exact Nat.add_le_add_right (liftedFirstCoefficient_degree_le P d) 1)
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j _
    split_ifs
    · exact (MvPolynomial.totalDegree_pow _ _).trans
        ((Nat.mul_le_mul_left 2 (liftedFirstCoefficient_degree_le P j)).trans (by omega))
    · simp only [MvPolynomial.totalDegree_zero, Nat.zero_le]

def degreePieceMassExponent (N b : ℕ) : ℕ := (N + 2).size + 2 * (b + 1)

theorem liftedFirstCoefficient_mass_le (P : MvPolynomial (Fin (n + 1)) ℤ) (j : ℕ) :
    MvMass.mass (liftedFirstCoefficient P j) ≤ MvMass.mass P :=
  (MvMass.rename_le _ _).trans (firstVariableCoefficient_mass_le P j)

theorem degreePiecePolynomial_mass_le (P : MvPolynomial (Fin (n + 1)) ℤ) (N d b : ℕ)
    (hb : MvMass.mass P ≤ 2 ^ b) : MvMass.mass (degreePiecePolynomial P N d) ≤ 2 ^ degreePieceMassExponent N b := by
  have hc (j : ℕ) : MvMass.mass (liftedFirstCoefficient P j) ≤ 2 ^ b :=
    (liftedFirstCoefficient_mass_le P j).trans hb
  have hbase : MvMass.mass ((liftedFirstCoefficient P d * MvPolynomial.X 0 - 1) ^ 2) ≤
      2 ^ (2 * (b + 1)) := by
    apply (MvMass.pow_le _ _).trans
    have hm : MvMass.mass (liftedFirstCoefficient P d * MvPolynomial.X 0 - 1) ≤ 2 ^ (b + 1) := by
      apply (MvMass.sub_le _ _).trans
      apply (Nat.add_le_add ((MvMass.mul_le _ _).trans (by simpa only [MvMass.X, Nat.mul_one] using hc d)) le_rfl).trans
      simp only [MvMass.one, pow_succ]
      have := Nat.one_le_two_pow (n := b)
      omega
    exact (Nat.pow_le_pow_left hm 2).trans_eq (by rw [← pow_mul, Nat.mul_comm])
  have hterms (j : ℕ) : MvMass.mass (if d < j then liftedFirstCoefficient P j ^ 2 else 0) ≤
      2 ^ (2 * (b + 1)) := by
    split_ifs
    · apply (MvMass.pow_le _ _).trans
      apply (Nat.pow_le_pow_left (hc j) 2).trans
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    · simp only [MvMass.zero, Nat.zero_le]
  rw [degreePiecePolynomial]
  apply (MvMass.add_le _ _).trans
  apply (Nat.add_le_add hbase ((MvMass.sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hterms j)))).trans
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
  calc
    _ = (N + 2) * 2 ^ (2 * (b + 1)) := by simp only [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ 2 ^ (N + 2).size * 2 ^ (2 * (b + 1)) := Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
    _ = _ := (pow_add 2 _ _).symm

end LeanCanny.CountingHierarchy

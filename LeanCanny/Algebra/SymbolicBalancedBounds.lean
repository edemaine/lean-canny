/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicBalancedCoordinates

/-! # Compositional bounds for symbolic rational coordinates

Denominator-cleared composition has explicit outer degree, parameter degree,
and total integer coefficient-mass bounds. These are algebraic bounds; no
native coefficient reader or metadata-computation hypothesis is suppressed.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicBalancedCoordinate
open Polynomial SymbolicScaledSquarefree
open scoped Classical BigOperators

theorem clear_mass (e : ℕ) (p n d : Polynomial Coefficient) (hp : p.natDegree ≤ e) (M : ℕ)
    (hn : NestedMass.mass n ≤ M) (hd : NestedMass.mass d ≤ M) :
    NestedMass.mass (UnivariateRational.clear e p n d) ≤ NestedMass.mass p * M ^ e := by
  have hf (k : ℕ) (hk : k ∈ Finset.range (e + 1)) :
      NestedMass.mass (C (p.coeff k) * n ^ k * d ^ (e - k)) ≤ coefficientMass (p.coeff k) * M ^ e := by
    have hk' : k ≤ e := by have := Finset.mem_range.mp hk; omega
    calc
      _ ≤ coefficientMass (p.coeff k) * NestedMass.mass (n ^ k) * NestedMass.mass (d ^ (e - k)) := by
        apply (NestedMass.mul_le _ _).trans
        rw [← NestedMass.C (p.coeff k)]
        exact Nat.mul_le_mul_right _ (NestedMass.mul_le _ _)
      _ ≤ coefficientMass (p.coeff k) * M ^ k * M ^ (e - k) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ ((NestedMass.pow_le _ _).trans (Nat.pow_le_pow_left hn _)))
          ((NestedMass.pow_le _ _).trans (Nat.pow_le_pow_left hd _))
      _ = _ := by rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hk']
  calc
    _ ≤ ∑ k ∈ Finset.range (e + 1), coefficientMass (p.coeff k) * M ^ e :=
      (NestedMass.sum_le _ _).trans (Finset.sum_le_sum hf)
    _ = NestedMass.mass p * M ^ e := by
      rw [← Finset.sum_mul, ← NestedMass.range_sum p (e + 1) (by omega)]

theorem clear_inner_degree (e : ℕ) (p n d : Polynomial Coefficient) (Ep Ei : ℕ)
    (hp : ∀ k, (p.coeff k).natDegree ≤ Ep)
    (hn : ∀ k, (n.coeff k).natDegree ≤ Ei)
    (hd : ∀ k, (d.coeff k).natDegree ≤ Ei) (j : ℕ) :
    ((UnivariateRational.clear e p n d).coeff j).natDegree ≤ Ep + e * Ei := by
  apply (PolynomialKronecker.inner_degree_iff_swap _ _).mpr ?_ j
  rw [UnivariateRational.clear, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hk' : k ≤ e := by have := Finset.mem_range.mp hk; omega
  rw [map_mul, map_mul, map_pow, map_pow, Polynomial.Bivariate.swap_C]
  calc
    _ ≤ (map C (p.coeff k)).natDegree +
        (Polynomial.Bivariate.swap n ^ k).natDegree +
        (Polynomial.Bivariate.swap d ^ (e - k)).natDegree :=
      natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)
    _ ≤ Ep + k * Ei + (e - k) * Ei :=
      Nat.add_le_add (Nat.add_le_add (natDegree_map_le.trans (hp k))
        (natDegree_pow_le.trans (Nat.mul_le_mul_left _
          ((PolynomialKronecker.inner_degree_iff_swap n Ei).mp hn))))
        (natDegree_pow_le.trans (Nat.mul_le_mul_left _
          ((PolynomialKronecker.inner_degree_iff_swap d Ei).mp hd)))
    _ = _ := by rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_of_le hk']

namespace Coordinate

theorem comp_mass (outer inner : Coordinate) (s b : ℕ)
    (hon : NestedMass.mass outer.numerator ≤ 2 ^ s) (hod : NestedMass.mass outer.denominator ≤ 2 ^ s)
    (hin : NestedMass.mass inner.numerator ≤ 2 ^ b) (hid : NestedMass.mass inner.denominator ≤ 2 ^ b) :
    NestedMass.mass (comp outer inner).numerator ≤ 2 ^ (s + outer.degree * b) ∧
      NestedMass.mass (comp outer inner).denominator ≤ 2 ^ (s + outer.degree * b) := by
  have hpow : 2 ^ s * (2 ^ b) ^ outer.degree = 2 ^ (s + outer.degree * b) := by
    rw [← pow_mul, ← pow_add, Nat.mul_comm b]
  exact ⟨(clear_mass _ _ _ _ (le_max_left _ _) _ hin hid).trans ((Nat.mul_le_mul_right _ hon).trans_eq hpow),
    (clear_mass _ _ _ _ (le_max_right _ _) _ hin hid).trans ((Nat.mul_le_mul_right _ hod).trans_eq hpow)⟩

theorem comp_inner_degree (outer inner : Coordinate) (Eo Ei : ℕ)
    (hon : ∀ k, (outer.numerator.coeff k).natDegree ≤ Eo)
    (hod : ∀ k, (outer.denominator.coeff k).natDegree ≤ Eo)
    (hin : ∀ k, (inner.numerator.coeff k).natDegree ≤ Ei)
    (hid : ∀ k, (inner.denominator.coeff k).natDegree ≤ Ei) (j : ℕ) :
    ((comp outer inner).numerator.coeff j).natDegree ≤ Eo + outer.degree * Ei ∧
      ((comp outer inner).denominator.coeff j).natDegree ≤ Eo + outer.degree * Ei :=
  ⟨clear_inner_degree _ _ _ _ _ _ hon hin hid j, clear_inner_degree _ _ _ _ _ _ hod hin hid j⟩

end Coordinate

end LeanCanny.Algebra.SymbolicBalancedCoordinate

namespace LeanCanny.Algebra.SymbolicBalancedTree
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open scoped Classical

noncomputable def innerBudget (a : ℕ → SeparablePolynomial) (E : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, i => E i
  | h + 1, i => ((node a h (2 * i)).polynomial.natDegree + (node a h (2 * i + 1)).polynomial.natDegree) *
      (innerBudget a E h (2 * i) + innerBudget a E h (2 * i + 1))

theorem inner_degree (a : ℕ → SeparablePolynomial) (E : ℕ → ℕ)
    (hE : ∀ i k, ((a i).polynomial.coeff k).natDegree ≤ E i) (h i k : ℕ) :
    ((node a h i).polynomial.coeff k).natDegree ≤ innerBudget a E h i := by
  induction h generalizing i k with
  | zero => exact hE i k
  | succ h ih => exact resultant_inner_degree _ _ _ _ _ (fun k => ih (2 * i) k) (fun k => ih (2 * i + 1) k) k

end LeanCanny.Algebra.SymbolicBalancedTree

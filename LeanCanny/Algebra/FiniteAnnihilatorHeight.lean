/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteAnnihilatorFiltering
public import LeanCanny.Algebra.BalancedPrimitiveMass
public import LeanCanny.Algebra.SquarefreeUniformBounds

/-! # Source-derived heights for finite annihilator construction

Original degrees at most D and coefficient magnitudes at most 2^b give the
common degree and mass-exponent bound (D+b+4)^(256*(n+1)^4). Its binary writer
is native polynomial-time when D,b are binary controls and n is unary.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteAnnihilatorTree
open Polynomial BalancedPrimitiveTree
open scoped BigOperators

def sourceHeight (D b n : ℕ) : ℕ := (D + b + 4) ^ (256 * (n + 1) ^ 4)

theorem sourceHeight_binary {D b n : List Bool → ℕ} (hD : BinaryFn D) (hb : BinaryFn b) (hn : UnaryFn n) :
    BinaryFn (fun c => sourceHeight (D c) (b c) (n c)) :=
  ((hD.add hb).add (BinaryFn.const 4)).powUnary ((UnaryFn.const 256).mul ((hn.add (UnaryFn.const 1)).pow_const 4))

theorem heightExponent_le (n : ℕ) : 16 ^ (n.size + 1) ≤ 256 * (n + 1) ^ 4 := by
  have hw : 2 ^ (n.size + 1) ≤ 4 * (n + 1) := by
    rw [pow_succ]
    have h := width_bound n
    omega
  calc
    _ = (2 ^ (n.size + 1)) ^ 4 := by
      rw [show (16 : ℕ) = 2 ^ 4 by decide, ← pow_mul, ← pow_mul]
      congr 1
      omega
    _ ≤ (4 * (n + 1)) ^ 4 := Nat.pow_le_pow_left hw 4
    _ = _ := by ring

variable (p : ℕ → ℤ[X]) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)
variable (D b : ℕ) (hD : ∀ i < n, (p i).natDegree ≤ D)
variable (hb : ∀ i < n, ∀ k, ((p i).coeff k).natAbs ≤ 2 ^ b)

include hD hb

theorem source_tree_bounds (h i : ℕ) (hh : h ≤ n.size) :
    UniformBounds (leaf p n hp) h i (sourceHeight D b n) := by
  let S := D + b + 4
  have hS : 4 ≤ S := by dsimp only [S]; omega
  have hST : S ≤ S ^ 16 := by simpa using Nat.pow_le_pow_right (n := S) (by omega) (show 1 ≤ 16 by decide)
  have hbase : 4 ≤ S ^ 16 := hS.trans hST
  have hd (i : ℕ) : (leaf p n hp i).polynomial.natDegree ≤ S ^ 16 := by
    by_cases hi : i < n
    · rw [leaf_degree p n hp i hi]
      exact (ScaledSquarefree.polynomial_natDegree_le _ (hp i hi)).trans
        (((hD i hi).trans (by dsimp only [S]; omega : D ≤ S)).trans hST)
    · rw [padding_degree p n hp i (by omega)]
      omega
  have hm (i : ℕ) : coefficientMass (leaf p n hp i).polynomial ≤ 2 ^ (S ^ 16) := by
    by_cases hi : i < n
    · let F : SeparableBits.Family := {
        polynomial _ := p i
        height _ := b
        coefficient_bound _ := hb i hi }
      rw [leaf, dite_eq_left hi]
      change coefficientMass (ScaledSquarefree.polynomial (p i)) ≤ 2 ^ (S ^ 16)
      exact SeparableBits.squarefree_mass_uniform F [] S hS
        ((hD i hi).trans (by dsimp only [S]; omega : D ≤ S)) (by dsimp only [F, S]; omega) (hp i hi)
    · rw [leaf, dite_eq_right hi]
      change coefficientMass (X : ℤ[X]) ≤ 2 ^ (S ^ 16)
      have hx : coefficientMass (X : ℤ[X]) = 1 := by simpa only [pow_one] using coefficientMass_X_pow 1
      rw [hx]
      exact Nat.one_le_two_pow
  have ht := uniform_bounds (leaf p n hp) (S ^ 16) hbase hd hm h i
  apply ht.mono
  calc
    (S ^ 16) ^ (16 ^ h) = S ^ (16 ^ (h + 1)) := by
      rw [← pow_mul, pow_succ]
      congr 1
      ring
    _ ≤ S ^ (16 ^ (n.size + 1)) := Nat.pow_le_pow_right (by omega)
      (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hh 1))
    _ ≤ S ^ (256 * (n + 1) ^ 4) := Nat.pow_le_pow_right (by omega) (heightExponent_le n)
    _ = sourceHeight D b n := rfl

theorem source_bounds : UniformBounds (leaf p n hp) n.size 0 (sourceHeight D b n) :=
  source_tree_bounds p n hp D b hD hb n.size 0 le_rfl

theorem parameter_mass_from_source : coefficientMass (parameter p n hp).polynomial ≤ 2 ^ sourceHeight D b n :=
  (source_bounds p n hp D b hD hb).parameterMass

theorem coordinate_mass_from_source (i : Fin n) :
    coefficientMass (numerator p n hp i) ≤ 2 ^ sourceHeight D b n ∧
    coefficientMass (denominator p n hp i) ≤ 2 ^ sourceHeight D b n :=
  ⟨(source_bounds p n hp D b hD hb).numeratorMass i.val, (source_bounds p n hp D b hD hb).denominatorMass i.val⟩

theorem constraint_mass_from_source (A : Fin n → ℕ) (f : MvPolynomial (Fin n) ℤ)
    (hA : ∀ i, f.degreeOf i ≤ A i) (s : ℕ) (hs : RationalSubstitution.sourceMass f ≤ 2 ^ s) :
    coefficientMass (constraint p n hp A f) ≤ 2 ^ (s + (∑ i, 2 * A i) * sourceHeight D b n) :=
  RationalSubstitution.coefficientMass_clearedWith_le_pow A f _ _ hA s (sourceHeight D b n) hs
    (fun i => (coordinate_mass_from_source p n hp D b hD hb i).1)
    (fun i => (coordinate_mass_from_source p n hp D b hD hb i).2)

end LeanCanny.Algebra.FiniteAnnihilatorTree

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicBalancedTree
public import LeanCanny.Algebra.BalancedPrimitiveVectors

/-! # A balanced primitive representation of an original finite bivariate family -/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicBalancedTree
open Polynomial
open BalancedPrimitiveTree (coordinate)
open scoped Classical

theorem valid_iff (a : ℕ → SymbolicPrimitivePair.SeparablePolynomial) (beta : ℝ) (h i : ℕ) (x : Values ℝ h) :
    valid a beta h i x ↔ ∀ j < 2 ^ h,
      (a (2 ^ h * i + j)).polynomial.eval₂ (SymbolicScaledSquarefree.scalarEvaluation beta) (coordinate h x j) = 0 := by
  induction h generalizing i with
  | zero =>
    constructor
    · intro hx j hj
      have hj' : j = 0 := by simp only [pow_zero] at hj; omega
      simpa only [pow_zero, one_mul, hj', Nat.add_zero, coordinate, valid] using hx
    · intro hx
      simpa only [pow_zero, one_mul, Nat.add_zero, coordinate, valid] using hx 0 (by decide)
  | succ h ih =>
    have hlbase : 2 ^ h * (2 * i) = 2 ^ (h + 1) * i := by rw [pow_succ]; ring
    have hrbase : 2 ^ h * (2 * i + 1) = 2 ^ (h + 1) * i + 2 ^ h := by rw [pow_succ]; ring
    rw [valid, ih, ih]
    constructor
    · rintro ⟨hl, hr⟩ j hj
      by_cases hjl : j < 2 ^ h
      · simpa only [coordinate, ite_eq_left hjl, hlbase] using hl j hjl
      · have hjr : j - 2 ^ h < 2 ^ h := by rw [pow_succ] at hj; omega
        have haddr : 2 ^ h * (2 * i + 1) + (j - 2 ^ h) = 2 ^ (h + 1) * i + j := by rw [hrbase]; omega
        simpa only [coordinate, ite_eq_right hjl, haddr] using hr (j - 2 ^ h) hjr
    · intro hx
      constructor
      · intro j hj
        have hj' : j < 2 ^ (h + 1) := by rw [pow_succ]; omega
        simpa only [coordinate, ite_eq_left hj, hlbase] using hx j hj'
      · intro j hj
        have hj' : 2 ^ h + j < 2 ^ (h + 1) := by rw [pow_succ]; omega
        have hjn : ¬ 2 ^ h + j < 2 ^ h := by omega
        have haddr : 2 ^ (h + 1) * i + (2 ^ h + j) = 2 ^ h * (2 * i + 1) + j := by rw [hrbase]; omega
        simpa only [coordinate, ite_eq_right hjn, Nat.add_sub_cancel_left, haddr] using hx (2 ^ h + j) hj'

end LeanCanny.Algebra.SymbolicBalancedTree

namespace LeanCanny.Algebra.SymbolicBalancedFinite
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open BalancedPrimitiveTree (coordinate tabulate coordinate_tabulate coordinate_injective)
open scoped Classical BigOperators

noncomputable def padding : SeparablePolynomial :=
  ⟨X, by simpa only [Polynomial.map_X] using (separable_X (R := CoefficientField))⟩

noncomputable def leaf (p : ℕ → Polynomial Coefficient) (n : ℕ)
    (hp : ∀ i < n, p i ≠ 0) (i : ℕ) : SeparablePolynomial :=
  if hi : i < n then SeparablePolynomial.of_nonzero (p i) (hp i hi) else padding

noncomputable def leafMass (p : ℕ → Polynomial Coefficient) (n : ℕ) (b : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < n then massExponent (p i).natDegree (b i) else 0

theorem leaf_coefficient_mass (p : ℕ → Polynomial Coefficient) (n : ℕ)
    (hp : ∀ i < n, p i ≠ 0) (b : ℕ → ℕ)
    (hm : ∀ i < n, ∀ k, coefficientMass ((p i).coeff k) ≤ 2 ^ b i) (i k : ℕ) :
    coefficientMass ((leaf p n hp i).polynomial.coeff k) ≤ 2 ^ leafMass p n b i := by
  by_cases hi : i < n
  · simpa only [leaf, leafMass, dite_eq_left hi, ite_eq_left hi,
      SeparablePolynomial.of_nonzero] using polynomial_coefficient_mass (p i) (b i) (hm i hi) k
  · have h1 : coefficientMass (1 : Coefficient) = 1 := by
      simpa only [Polynomial.C_1, Int.natAbs_one] using coefficientMass_C (1 : ℤ)
    simp only [leaf, leafMass, dite_eq_right hi, ite_eq_right hi, padding, coeff_X, pow_zero]
    split_ifs <;> simp only [h1, coefficientMass_zero, le_refl, Nat.zero_le]

noncomputable def parameter (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0) : Polynomial Coefficient :=
  (SymbolicBalancedTree.node (leaf p n hp) n.size 0).polynomial

noncomputable def exponent (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0) (b : ℕ → ℕ) : ℕ :=
  SymbolicBalancedTree.exponent (leaf p n hp) (leafMass p n b) n.size 0 +
    ∑ i ∈ Finset.range n, SymbolicScaledSquarefree.smallExponent (p i).natDegree (b i)

noncomputable def decode (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)
    (beta theta : ℝ) : Fin n → ℝ :=
  fun i => coordinate n.size (SymbolicBalancedTree.decode (leaf p n hp) beta n.size 0 theta) i.val

noncomputable def paddedValues (n : ℕ) (x : Fin n → ℝ) : SymbolicBalancedTree.Values ℝ n.size :=
  tabulate n.size (fun j => if hj : j < n then x ⟨j, hj⟩ else 0)

noncomputable def encode (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)
    (x : Fin n → ℝ) : ℝ :=
  SymbolicBalancedTree.encode (leaf p n hp) n.size 0 (paddedValues n x)

private theorem tree_threshold (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)
    (b : ℕ → ℕ) (beta : ℝ) (he : beta ≤ InfinitesimalSign.dyadic (exponent p n hp b)) :
    beta ≤ InfinitesimalSign.dyadic
      (SymbolicBalancedTree.exponent (leaf p n hp) (leafMass p n b) n.size 0) :=
  he.trans (dyadic_antitone (by unfold exponent; omega))

private theorem leaf_threshold (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)
    (b : ℕ → ℕ) (beta : ℝ) (he : beta ≤ InfinitesimalSign.dyadic (exponent p n hp b))
    (i : ℕ) (hi : i < n) :
    beta ≤ InfinitesimalSign.dyadic (SymbolicScaledSquarefree.smallExponent (p i).natDegree (b i)) := by
  apply he.trans
  apply dyadic_antitone
  have h := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr hi) (f := fun i => SymbolicScaledSquarefree.smallExponent (p i).natDegree (b i))
  unfold exponent
  omega

private theorem leaf_root_iff (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)
    (b : ℕ → ℕ) (hm : ∀ i < n, ∀ k, coefficientMass ((p i).coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (exponent p n hp b))
    (i : ℕ) (hi : i < n) (x : ℝ) :
    (leaf p n hp i).polynomial.eval₂ (scalarEvaluation beta) x = 0 ↔
      (p i).eval₂ (scalarEvaluation beta) x = 0 := by
  simpa only [leaf, dite_eq_left hi, SeparablePolynomial.of_nonzero] using
    SymbolicScaledSquarefree.small_roots_iff (p i) (hp i hi) (b i) (hm i hi) beta hb
      (leaf_threshold p n hp b beta he i hi) x

theorem decode_root (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)
    (b : ℕ → ℕ) (hm : ∀ i < n, ∀ k, coefficientMass ((p i).coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (exponent p n hp b))
    (theta : ℝ) (ht : (parameter p n hp).eval₂ (scalarEvaluation beta) theta = 0) (i : Fin n) :
    (p i.val).eval₂ (scalarEvaluation beta) (decode p n hp beta theta i) = 0 := by
  have hr := SymbolicBalancedTree.decode_root (leaf p n hp) (leafMass p n b)
    (leaf_coefficient_mass p n hp b hm) beta hb n.size 0 (tree_threshold p n hp b beta he) theta ht
  have hc := (SymbolicBalancedTree.valid_iff (leaf p n hp) beta n.size 0 _).mp hr.1
    i.val (i.isLt.trans (Nat.lt_size_self n))
  simp only [Nat.mul_zero, Nat.zero_add] at hc
  exact (leaf_root_iff p n hp b hm beta hb he i.val i.isLt _).mp hc

theorem encode_roots (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)
    (b : ℕ → ℕ) (hm : ∀ i < n, ∀ k, coefficientMass ((p i).coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (exponent p n hp b))
    (x : Fin n → ℝ) (hx : ∀ i, (p i.val).eval₂ (scalarEvaluation beta) (x i) = 0) :
    (parameter p n hp).eval₂ (scalarEvaluation beta) (encode p n hp x) = 0 ∧
      decode p n hp beta (encode p n hp x) = x := by
  have hv : SymbolicBalancedTree.valid (leaf p n hp) beta n.size 0 (paddedValues n x) := by
    rw [SymbolicBalancedTree.valid_iff]
    intro j hj
    simp only [Nat.mul_zero, Nat.zero_add, paddedValues, coordinate_tabulate _ _ j hj]
    by_cases hjn : j < n
    · rw [dite_eq_left hjn]
      exact (leaf_root_iff p n hp b hm beta hb he j hjn _).mpr (hx ⟨j, hjn⟩)
    · simp only [dite_eq_right hjn, leaf, padding, Polynomial.eval₂_X]
  have hr := SymbolicBalancedTree.encode_valid (leaf p n hp) (leafMass p n b)
    (leaf_coefficient_mass p n hp b hm) beta hb n.size 0 (tree_threshold p n hp b beta he) _ hv
  refine ⟨hr.1, ?_⟩
  funext i
  change coordinate n.size (SymbolicBalancedTree.decode (leaf p n hp) beta n.size 0
    (SymbolicBalancedTree.encode (leaf p n hp) n.size 0 (paddedValues n x))) i.val = x i
  rw [hr.2, paddedValues, coordinate_tabulate _ _ i.val (i.isLt.trans (Nat.lt_size_self n)), dite_eq_left i.isLt]

theorem encode_decode (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)
    (b : ℕ → ℕ) (hm : ∀ i < n, ∀ k, coefficientMass ((p i).coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (exponent p n hp b))
    (theta : ℝ) (ht : (parameter p n hp).eval₂ (scalarEvaluation beta) theta = 0) :
    encode p n hp (decode p n hp beta theta) = theta := by
  have hr := SymbolicBalancedTree.decode_root (leaf p n hp) (leafMass p n b)
    (leaf_coefficient_mass p n hp b hm) beta hb n.size 0 (tree_threshold p n hp b beta he) theta ht
  have hv : paddedValues n (decode p n hp beta theta) = SymbolicBalancedTree.decode (leaf p n hp) beta n.size 0 theta := by
    apply coordinate_injective
    intro j hj
    rw [paddedValues, coordinate_tabulate _ _ j hj]
    by_cases hjn : j < n
    · rw [dite_eq_left hjn]
      rfl
    · rw [dite_eq_right hjn]
      have h := (SymbolicBalancedTree.valid_iff (leaf p n hp) beta n.size 0 _).mp hr.1 j hj
      simp only [Nat.mul_zero, Nat.zero_add, leaf, dite_eq_right hjn, padding, Polynomial.eval₂_X] at h
      exact h.symm
  change SymbolicBalancedTree.encode (leaf p n hp) n.size 0 (paddedValues n (decode p n hp beta theta)) = theta
  rw [hv]
  exact hr.2

noncomputable def rootEquiv (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)
    (b : ℕ → ℕ) (hm : ∀ i < n, ∀ k, coefficientMass ((p i).coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (exponent p n hp b)) :
    {theta : ℝ // (parameter p n hp).eval₂ (scalarEvaluation beta) theta = 0} ≃
      {x : Fin n → ℝ // ∀ i, (p i.val).eval₂ (scalarEvaluation beta) (x i) = 0} where
  toFun theta := ⟨decode p n hp beta theta.val, decode_root p n hp b hm beta hb he theta.val theta.property⟩
  invFun x := ⟨encode p n hp x.val, (encode_roots p n hp b hm beta hb he x.val x.property).1⟩
  left_inv theta := Subtype.ext (encode_decode p n hp b hm beta hb he theta.val theta.property)
  right_inv x := Subtype.ext (encode_roots p n hp b hm beta hb he x.val x.property).2

end LeanCanny.Algebra.SymbolicBalancedFinite


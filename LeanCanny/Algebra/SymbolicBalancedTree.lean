/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicPrimitivePairRaw
public import LeanCanny.Algebra.BalancedPrimitiveCoordinates

/-! # A constructed balanced symbolic primitive tree

The polynomial, all separating directions, coefficient-mass budgets, and a
common ordinary-specialization threshold are recursive constructions. Below
that threshold, real roots correspond bijectively to all leaf-root tuples.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicBalancedTree
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open scoped Classical BigOperators
attribute [local irreducible] Matrix.det

abbrev Values := BalancedPrimitiveTree.Values

noncomputable def node (a : ℕ → SeparablePolynomial) : ℕ → ℕ → SeparablePolynomial
  | 0, i => a i
  | h + 1, i => combine (node a h (2 * i)) (node a h (2 * i + 1))

noncomputable def massBudget (a : ℕ → SeparablePolynomial) (b : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, i => b i
  | h + 1, i => resultantMassExponent (node a h (2 * i)).polynomial.natDegree
      (node a h (2 * i + 1)).polynomial.natDegree
      (direction (node a h (2 * i)) (node a h (2 * i + 1)))
      (massBudget a b h (2 * i)) (massBudget a b h (2 * i + 1))

theorem coefficient_mass (a : ℕ → SeparablePolynomial) (b : ℕ → ℕ)
    (hb : ∀ i k, coefficientMass ((a i).polynomial.coeff k) ≤ 2 ^ b i) (h i k : ℕ) :
    coefficientMass ((node a h i).polynomial.coeff k) ≤ 2 ^ massBudget a b h i := by
  induction h generalizing i k with
  | zero => exact hb i k
  | succ h ih =>
    exact (NestedMass.coeff_le _ k).trans
      (resultant_mass _ _ _ _ _ (fun k => ih (2 * i) k) (fun k => ih (2 * i + 1) k))

theorem degree_tree (a : ℕ → SeparablePolynomial) (h i : ℕ) :
    (node a h i).polynomial.natDegree = BalancedProduct.tree (fun j => (a j).polynomial.natDegree) h i := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih => rw [node]; exact (parameter_natDegree _ _).trans (by rw [ih, ih]; rfl)

theorem degree_eq_prod (a : ℕ → SeparablePolynomial) (h i : ℕ) :
    (node a h i).polynomial.natDegree =
      ∏ j ∈ Finset.range (2 ^ h), (a (2 ^ h * i + j)).polynomial.natDegree :=
  (degree_tree a h i).trans (BalancedProduct.tree_eq_prod _ h i)

noncomputable def exponent (a : ℕ → SeparablePolynomial) (b : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, i => b i + gcdMassExponent (a i).polynomial.natDegree (b i) + 1
  | h + 1, i => exponent a b h (2 * i) + exponent a b h (2 * i + 1) +
      smallExponent (node a h (2 * i)) (node a h (2 * i + 1))
        (massBudget a b h (2 * i)) (massBudget a b h (2 * i + 1))

noncomputable def valid (a : ℕ → SeparablePolynomial) (beta : ℝ) : (h : ℕ) → ℕ → Values ℝ h → Prop
  | 0, i, x => (a i).polynomial.eval₂ (scalarEvaluation beta) x = 0
  | h + 1, i, x => valid a beta h (2 * i) x.1 ∧ valid a beta h (2 * i + 1) x.2

noncomputable def decode (a : ℕ → SeparablePolynomial) (beta : ℝ) : (h : ℕ) → ℕ → ℝ → Values ℝ h
  | 0, _, theta => theta
  | h + 1, i, theta =>
    let z := evaluatedCoordinates (scalarEvaluation beta) (node a h (2 * i)) (node a h (2 * i + 1)) theta
    (decode a beta h (2 * i) z.1, decode a beta h (2 * i + 1) z.2)

noncomputable def encode (a : ℕ → SeparablePolynomial) : (h : ℕ) → ℕ → Values ℝ h → ℝ
  | 0, _, x => x
  | h + 1, i, x => shear (direction (node a h (2 * i)) (node a h (2 * i + 1)))
    (encode a h (2 * i) x.1, encode a h (2 * i + 1) x.2)

private theorem child_thresholds (a : ℕ → SeparablePolynomial) (b : ℕ → ℕ) (h i : ℕ)
    (beta : ℝ) (he : beta ≤ InfinitesimalSign.dyadic (exponent a b (h + 1) i)) :
    beta ≤ InfinitesimalSign.dyadic (exponent a b h (2 * i)) ∧
      beta ≤ InfinitesimalSign.dyadic (exponent a b h (2 * i + 1)) ∧
      beta ≤ InfinitesimalSign.dyadic (smallExponent (node a h (2 * i)) (node a h (2 * i + 1))
        (massBudget a b h (2 * i)) (massBudget a b h (2 * i + 1))) := by
  refine ⟨he.trans (dyadic_antitone ?_), he.trans (dyadic_antitone ?_), he.trans (dyadic_antitone ?_)⟩ <;>
    rw [exponent] <;> omega

theorem decode_root (a : ℕ → SeparablePolynomial) (b : ℕ → ℕ)
    (hm : ∀ i k, coefficientMass ((a i).polynomial.coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (h i : ℕ)
    (he : beta ≤ InfinitesimalSign.dyadic (exponent a b h i)) (theta : ℝ)
    (ht : (node a h i).polynomial.eval₂ (scalarEvaluation beta) theta = 0) :
    valid a beta h i (decode a beta h i theta) ∧ encode a h i (decode a beta h i theta) = theta := by
  induction h generalizing i theta with
  | zero => exact ⟨ht, rfl⟩
  | succ h ih =>
    obtain ⟨hel, her, hep⟩ := child_thresholds a b h i beta he
    have hr := small_decode_root (node a h (2 * i)) (node a h (2 * i + 1))
      (massBudget a b h (2 * i)) (massBudget a b h (2 * i + 1))
      (coefficient_mass a b hm h (2 * i)) (coefficient_mass a b hm h (2 * i + 1)) beta hb hep theta ht
    have hl := ih (2 * i) hel _ hr.1
    have hh := ih (2 * i + 1) her _ hr.2.1
    refine ⟨⟨hl.1, hh.1⟩, ?_⟩
    simp only [decode, encode]
    rw [hl.2, hh.2]
    exact hr.2.2.1

theorem encode_valid (a : ℕ → SeparablePolynomial) (b : ℕ → ℕ)
    (hm : ∀ i k, coefficientMass ((a i).polynomial.coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (h i : ℕ)
    (he : beta ≤ InfinitesimalSign.dyadic (exponent a b h i)) (x : Values ℝ h)
    (hx : valid a beta h i x) :
    (node a h i).polynomial.eval₂ (scalarEvaluation beta) (encode a h i x) = 0 ∧
      decode a beta h i (encode a h i x) = x := by
  induction h generalizing i with
  | zero => exact ⟨hx, rfl⟩
  | succ h ih =>
    obtain ⟨hel, her, hep⟩ := child_thresholds a b h i beta he
    have hl := ih (2 * i) hel x.1 hx.1
    have hh := ih (2 * i + 1) her x.2 hx.2
    have hr := small_encode_roots (node a h (2 * i)) (node a h (2 * i + 1))
      (massBudget a b h (2 * i)) (massBudget a b h (2 * i + 1))
      (coefficient_mass a b hm h (2 * i)) (coefficient_mass a b hm h (2 * i + 1)) beta hb hep _ _ hl.1 hh.1
    refine ⟨hr.1, ?_⟩
    simp only [decode, encode]
    rw [hr.2]
    exact Prod.ext hl.2 hh.2

noncomputable def rootEquiv (a : ℕ → SeparablePolynomial) (b : ℕ → ℕ)
    (hm : ∀ i k, coefficientMass ((a i).polynomial.coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (h i : ℕ)
    (he : beta ≤ InfinitesimalSign.dyadic (exponent a b h i)) :
    {theta : ℝ // (node a h i).polynomial.eval₂ (scalarEvaluation beta) theta = 0} ≃
      {x : Values ℝ h // valid a beta h i x} where
  toFun theta := ⟨decode a beta h i theta.val, (decode_root a b hm beta hb h i he theta.val theta.property).1⟩
  invFun x := ⟨encode a h i x.val, (encode_valid a b hm beta hb h i he x.val x.property).1⟩
  left_inv theta := Subtype.ext (decode_root a b hm beta hb h i he theta.val theta.property).2
  right_inv x := Subtype.ext (encode_valid a b hm beta hb h i he x.val x.property).2

end LeanCanny.Algebra.SymbolicBalancedTree

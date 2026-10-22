/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SeparableIntegerPolynomialField
public import LeanCanny.Algebra.BalancedProduct

/-! # Balanced primitive parameters for finite products of root sets

Every internal node uses the canonical bounded direction scan and the explicit
integer resultant. Decoding follows the explicit rational pair coordinates.
The depth is a parameter of the construction; a uniform space evaluator is
not asserted by these algebraic recursion proofs.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedPrimitiveTree
open Polynomial
open scoped BigOperators

noncomputable def node (a : ℕ → SeparableIntegerPolynomial) : ℕ → ℕ → SeparableIntegerPolynomial
  | 0, i => a i
  | h + 1, i => (node a h (2 * i)).combine (node a h (2 * i + 1))

theorem degree_tree (a : ℕ → SeparableIntegerPolynomial) (h i : ℕ) :
    (node a h i).polynomial.natDegree = BalancedProduct.tree (fun j => (a j).polynomial.natDegree) h i := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih => rw [node, SeparableIntegerPolynomial.combine_degree, ih, ih]; rfl

theorem degree_eq_prod (a : ℕ → SeparableIntegerPolynomial) (h i : ℕ) :
    (node a h i).polynomial.natDegree = ∏ j ∈ Finset.range (2 ^ h), (a (2 ^ h * i + j)).polynomial.natDegree :=
  (degree_tree a h i).trans (BalancedProduct.tree_eq_prod _ h i)

theorem degree_le_pow (a : ℕ → SeparableIntegerPolynomial) (h i D : ℕ)
    (ha : ∀ j < 2 ^ h, (a (2 ^ h * i + j)).polynomial.natDegree ≤ D) :
    (node a h i).polynomial.natDegree ≤ D ^ (2 ^ h) := by
  rw [degree_eq_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.range (2 ^ h), D := Finset.prod_le_prod (fun j hj => ha j (Finset.mem_range.mp hj))
    _ = _ := by simp

def Values (L : Type*) : ℕ → Type _
  | 0 => L
  | h + 1 => Values L h × Values L h

variable {L : Type*} [Field L] [CharZero L]

def valid (a : ℕ → SeparableIntegerPolynomial) : (h : ℕ) → ℕ → Values L h → Prop
  | 0, i, x => (a i).polynomial.eval₂ (Int.castRingHom L) x = 0
  | h + 1, i, x => valid a h (2 * i) x.1 ∧ valid a h (2 * i + 1) x.2

noncomputable def decode (a : ℕ → SeparableIntegerPolynomial) : (h : ℕ) → ℕ → L → Values L h
  | 0, _, theta => theta
  | h + 1, i, theta =>
    let z := (node a h (2 * i)).decode (node a h (2 * i + 1)) theta
    (decode a h (2 * i) z.1, decode a h (2 * i + 1) z.2)

noncomputable def encode (a : ℕ → SeparableIntegerPolynomial) : (h : ℕ) → ℕ → Values L h → L
  | 0, _, x => x
  | h + 1, i, x => (node a h (2 * i)).encode (node a h (2 * i + 1))
      (encode a h (2 * i) x.1) (encode a h (2 * i + 1) x.2)

theorem decode_root (a : ℕ → SeparableIntegerPolynomial) (h i : ℕ) (theta : L)
    (ht : (node a h i).polynomial.eval₂ (Int.castRingHom L) theta = 0) :
    valid a h i (decode a h i theta) ∧ encode a h i (decode a h i theta) = theta := by
  induction h generalizing i theta with
  | zero => exact ⟨ht, rfl⟩
  | succ h ih =>
    have hr := SeparableIntegerPolynomial.decode_root_over (node a h (2 * i)) (node a h (2 * i + 1)) theta ht
    have hl := ih (2 * i) _ hr.1
    have hh := ih (2 * i + 1) _ hr.2.1
    exact ⟨⟨hl.1, hh.1⟩, by
      simp only [encode, decode]
      rw [hl.2, hh.2]
      exact hr.2.2⟩

theorem encode_valid (a : ℕ → SeparableIntegerPolynomial) (h i : ℕ) (x : Values L h)
    (hx : valid a h i x) :
    (node a h i).polynomial.eval₂ (Int.castRingHom L) (encode a h i x) = 0 ∧
      decode a h i (encode a h i x) = x := by
  induction h generalizing i with
  | zero => exact ⟨hx, rfl⟩
  | succ h ih =>
    have hl := ih (2 * i) x.1 hx.1
    have hr := ih (2 * i + 1) x.2 hx.2
    refine ⟨SeparableIntegerPolynomial.encode_root_over _ _ _ _ hl.1 hr.1, ?_⟩
    change (decode a h (2 * i) ((node a h (2 * i)).decode (node a h (2 * i + 1))
      ((node a h (2 * i)).encode (node a h (2 * i + 1)) _ _)).1,
      decode a h (2 * i + 1) ((node a h (2 * i)).decode (node a h (2 * i + 1))
      ((node a h (2 * i)).encode (node a h (2 * i + 1)) _ _)).2) = x
    rw [SeparableIntegerPolynomial.decode_encode_over _ _ _ _ hl.1 hr.1]
    exact Prod.ext hl.2 hr.2

noncomputable def rootEquiv (a : ℕ → SeparableIntegerPolynomial) (h i : ℕ) :
    {theta : L // (node a h i).polynomial.eval₂ (Int.castRingHom L) theta = 0} ≃
      {x : Values L h // valid a h i x} where
  toFun theta := ⟨decode a h i theta.val, (decode_root a h i theta.val theta.property).1⟩
  invFun x := ⟨encode a h i x.val, (encode_valid a h i x.val x.property).1⟩
  left_inv theta := Subtype.ext (decode_root a h i theta.val theta.property).2
  right_inv x := Subtype.ext (encode_valid a h i x.val x.property).2

end LeanCanny.Algebra.BalancedPrimitiveTree

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicBalancedFinite
public import LeanCanny.Algebra.SymbolicBalancedCoordinates

/-! # Original finite-root coordinates as actual bivariate rational formulas -/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicBalancedFinite
open Polynomial SymbolicScaledSquarefree
open scoped Classical

noncomputable def coordinate (p : ℕ → Polynomial Coefficient) (n : ℕ)
    (hp : ∀ i < n, p i ≠ 0) (i : Fin n) : SymbolicBalancedCoordinate.Coordinate :=
  SymbolicBalancedCoordinate.coordinate (leaf p n hp) n.size 0 i.val

theorem coordinate_spec (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)
    (b : ℕ → ℕ) (hm : ∀ i < n, ∀ k, coefficientMass ((p i).coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (exponent p n hp b))
    (theta : ℝ) (ht : (parameter p n hp).eval₂ (scalarEvaluation beta) theta = 0) (i : Fin n) :
    (coordinate p n hp i).denominator.eval₂ (scalarEvaluation beta) theta ≠ 0 ∧
      (coordinate p n hp i).eval (scalarEvaluation beta) theta = decode p n hp beta theta i := by
  have he' : beta ≤ InfinitesimalSign.dyadic
      (SymbolicBalancedTree.exponent (leaf p n hp) (leafMass p n b) n.size 0) :=
    he.trans (SymbolicPrimitivePair.dyadic_antitone (by unfold exponent; omega))
  exact SymbolicBalancedCoordinate.coordinate_spec (leaf p n hp) (leafMass p n b)
    (leaf_coefficient_mass p n hp b hm) beta hb n.size 0 i.val
      (i.isLt.trans (Nat.lt_size_self n)) he' theta ht

theorem coordinate_root (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)
    (b : ℕ → ℕ) (hm : ∀ i < n, ∀ k, coefficientMass ((p i).coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (exponent p n hp b))
    (theta : ℝ) (ht : (parameter p n hp).eval₂ (scalarEvaluation beta) theta = 0) (i : Fin n) :
    (p i.val).eval₂ (scalarEvaluation beta) ((coordinate p n hp i).eval (scalarEvaluation beta) theta) = 0 := by
  rw [(coordinate_spec p n hp b hm beta hb he theta ht i).2]
  exact decode_root p n hp b hm beta hb he theta ht i

theorem coordinates_encode (p : ℕ → Polynomial Coefficient) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)
    (b : ℕ → ℕ) (hm : ∀ i < n, ∀ k, coefficientMass ((p i).coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (exponent p n hp b))
    (x : Fin n → ℝ) (hx : ∀ i, (p i.val).eval₂ (scalarEvaluation beta) (x i) = 0) (i : Fin n) :
    (coordinate p n hp i).eval (scalarEvaluation beta) (encode p n hp x) = x i := by
  have hr := encode_roots p n hp b hm beta hb he x hx
  rw [(coordinate_spec p n hp b hm beta hb he _ hr.1 i).2, hr.2]

end LeanCanny.Algebra.SymbolicBalancedFinite

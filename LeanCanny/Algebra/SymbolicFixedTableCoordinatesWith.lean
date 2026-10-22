/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableCoordinateBounds
public import LeanCanny.Algebra.SymbolicCoordinateCompositionWith

/-! # Fixed-envelope coordinates for the prepared symbolic table

Each level clears with its public sixteenth-power envelope. Evaluation and
nonzero denominators agree with the decoded original leaves; polynomial
representatives need not equal the minimal-degree representatives.
-/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicFixedTable
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open SymbolicBalancedCoordinate (Coordinate)
open scoped Classical

private theorem fixed_composition_exponent (T e : ℕ) (hT : 4 ≤ T) (he : e ≤ T) : T + e * T ^ 12 ≤ T ^ 16 := by
  have h1 : T ≤ T ^ 13 := by simpa using Nat.pow_le_pow_right (n := T) (by omega) (show 1 ≤ 13 by decide)
  have hm : e * T ^ 12 ≤ T ^ 13 := (Nat.mul_le_mul_right _ he).trans_eq (by ring)
  exact (by omega : T + e * T ^ 12 ≤ 16 * T ^ 13).trans
    ((CannyResultantBits.sixteen_mul_pow_le T 13 hT).trans (Nat.pow_le_pow_right (by omega) (by decide)))

theorem CoordinateBounds.compWith {r s : Coordinate} {T : ℕ} (hT : 4 ≤ T)
    (hr : CoordinateBounds r T) (hs : CoordinateBounds s (T ^ 12)) :
    CoordinateBounds (Coordinate.compWith T r s) (T ^ 16) := by
  have he := fixed_composition_exponent T T hT le_rfl
  have hpow : 2 ^ T * (2 ^ (T ^ 12)) ^ T = 2 ^ (T + T * T ^ 12) := by
    rw [← pow_mul, ← pow_add, Nat.mul_comm (T ^ 12)]
  have hm (p : Polynomial Coefficient) (hp : p.natDegree ≤ T)
      (hm : NestedMass.mass p ≤ 2 ^ T) :
      NestedMass.mass (UnivariateRational.clear T p s.numerator s.denominator) ≤ 2 ^ (T ^ 16) :=
    ((SymbolicBalancedCoordinate.clear_mass T p _ _ hp _ hs.numeratorMass hs.denominatorMass).trans
      ((Nat.mul_le_mul_right _ hm).trans_eq hpow)).trans (Nat.pow_le_pow_right (by decide) he)
  refine ⟨(Coordinate.compWith_degree T r s).trans
    ((Nat.mul_le_mul_left _ hs.degree).trans ?_), ?_, ?_,
    hm _ ((le_max_left _ _).trans hr.degree) hr.numeratorMass,
    hm _ ((le_max_right _ _).trans hr.degree) hr.denominatorMass⟩
  · exact (show T * T ^ 12 = T ^ 13 by ring).le.trans (Nat.pow_le_pow_right (by omega) (by decide))
  · intro k
    exact (SymbolicBalancedCoordinate.clear_inner_degree T _ _ _ T (T ^ 12)
      hr.numeratorInner hs.numeratorInner hs.denominatorInner k).trans he
  · intro k
    exact (SymbolicBalancedCoordinate.clear_inner_degree T _ _ _ T (T ^ 12)
      hr.denominatorInner hs.numeratorInner hs.denominatorInner k).trans he

noncomputable def coordinateWith (T : ℕ) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ) :
    ℕ → ℕ → ℕ → Coordinate
  | 0, _, _ => SymbolicBalancedCoordinate.identity
  | h + 1, i, j => if j < 2 ^ h then
      Coordinate.compWith (T ^ (16 ^ h)) (coordinateWith T a c h (2 * i) j)
        (pairCoordinate false (node a c h (2 * i)) (node a c h (2 * i + 1)) (c h i))
    else Coordinate.compWith (T ^ (16 ^ h)) (coordinateWith T a c h (2 * i + 1) (j - 2 ^ h))
      (pairCoordinate true (node a c h (2 * i)) (node a c h (2 * i + 1)) (c h i))

theorem coordinateWith_uniform (B : Budget) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ)
    (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c) (T : ℕ) (hT : 4 ≤ T) (hB : B.BoundedBy T) (h i j : ℕ) :
    CoordinateBounds (coordinateWith T a c h i j) (T ^ (16 ^ h)) := by
  induction h generalizing i j with
  | zero => simpa only [coordinateWith, pow_zero, pow_one] using identity_bounds T (by omega)
  | succ h ih =>
    have ht : T ≤ T ^ (16 ^ h) := by
      simpa only [pow_one] using Nat.pow_le_pow_right (n := T) (by omega) (Nat.one_le_pow h 16 (by decide))
    have hp (right : Bool) := pairCoordinate_bounds (treeBudget B h) _ (hT.trans ht) (treeBudget_bounded B T hT hB h)
      (node a c h (2 * i)) (node a c h (2 * i + 1)) (node_controls B a c ha hc h (2 * i))
      (node_controls B a c ha hc h (2 * i + 1)) (c h i) (hc h i) right
    by_cases hj : j < 2 ^ h
    · rw [coordinateWith, ite_eq_left hj]
      simpa only [← pow_mul, pow_succ (16 : ℕ) h] using (ih (2 * i) j).compWith (hT.trans ht) (hp false)
    · rw [coordinateWith, ite_eq_right hj]
      simpa only [← pow_mul, pow_succ (16 : ℕ) h] using (ih (2 * i + 1) (j - 2 ^ h)).compWith (hT.trans ht) (hp true)


theorem coordinateWith_spec (B : Budget) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ)
    (T : ℕ) (hT : 4 ≤ T) (hB : B.BoundedBy T)
    (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c) (height : ℕ) (hs : SeparableTable a c height)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (referenceExponent B height))
    (h i j : ℕ) (hh : h ≤ height) (hj : j < 2 ^ h) (theta : ℝ)
    (ht : (node a c h i).eval₂ (scalarEvaluation beta) theta = 0) :
    (coordinateWith T a c h i j).denominator.eval₂ (scalarEvaluation beta) theta ≠ 0 ∧
      (coordinateWith T a c h i j).eval (scalarEvaluation beta) theta =
        BalancedPrimitiveTree.coordinate h (decode a c beta h i theta) j := by
  induction h generalizing i j theta with
  | zero => simp only [coordinateWith, SymbolicBalancedCoordinate.identity, Polynomial.eval₂_one,
      one_ne_zero, ne_eq, not_false_eq_true, Coordinate.eval, Polynomial.eval₂_X, div_one,
      decode, BalancedPrimitiveTree.coordinate, and_self]
  | succ h ih =>
    have hr := pair_decode_root (scalarEvaluation beta) (node a c h (2 * i)) (node a c h (2 * i + 1))
      (c h i) theta (node_degree_map B a c ha hc height h (2 * i) (by omega) beta hb he)
      (node_degree_map B a c ha hc height h (2 * i + 1) (by omega) beta hb he)
      (specialized_node_separable B a c ha hc height hs beta hb he h (2 * i) (by omega))
      (specialized_node_separable B a c ha hc height hs beta hb he h (2 * i + 1) (by omega))
      (specialized_node_separable B a c ha hc height hs beta hb he (h + 1) i hh) ht
    by_cases hjl : j < 2 ^ h
    · have hl := ih (2 * i) j (by omega) hjl _ hr.1
      have hd : (pairCoordinate false (node a c h (2 * i)) (node a c h (2 * i + 1)) (c h i)).denominator.eval₂
          (scalarEvaluation beta) theta ≠ 0 := hr.2.2.2
      refine ⟨?_, ?_⟩
      · rw [coordinateWith, ite_eq_left hjl]
        exact Coordinate.compWith_denominator_ne_zero _ _ _
          (coordinateWith_uniform B a c ha hc T hT hB _ _ _).degree _ _ hd hl.1
      · rw [coordinateWith, ite_eq_left hjl, Coordinate.eval_compWith _ _ _
          (coordinateWith_uniform B a c ha hc T hT hB _ _ _).degree _ _ hd]
        simpa only [decode, BalancedPrimitiveTree.coordinate, ite_eq_left hjl, eval_pairCoordinate_false] using hl.2
    · have hjr : j - 2 ^ h < 2 ^ h := by rw [pow_succ] at hj; omega
      have hh' := ih (2 * i + 1) (j - 2 ^ h) (by omega) hjr _ hr.2.1
      have hd : (pairCoordinate true (node a c h (2 * i)) (node a c h (2 * i + 1)) (c h i)).denominator.eval₂
          (scalarEvaluation beta) theta ≠ 0 := hr.2.2.2
      refine ⟨?_, ?_⟩
      · rw [coordinateWith, ite_eq_right hjl]
        exact Coordinate.compWith_denominator_ne_zero _ _ _
          (coordinateWith_uniform B a c ha hc T hT hB _ _ _).degree _ _ hd hh'.1
      · rw [coordinateWith, ite_eq_right hjl, Coordinate.eval_compWith _ _ _
          (coordinateWith_uniform B a c ha hc T hT hB _ _ _).degree _ _ hd]
        simpa only [decode, BalancedPrimitiveTree.coordinate, ite_eq_right hjl, eval_pairCoordinate_true] using hh'.2

end LeanCanny.Algebra.SymbolicFixedTable

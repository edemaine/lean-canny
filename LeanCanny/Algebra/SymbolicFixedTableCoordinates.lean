/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableUniformPreparation

/-! # Bivariate rational coordinates for the actual integer-prepared table

Each path composes the original arbitrary-direction pair formulas by scaled
polynomial clearing. Every resulting denominator is nonzero on every root,
and evaluation gives exactly the decoded original leaf coordinate.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTable
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open SymbolicBalancedCoordinate (Coordinate)
open scoped Classical

theorem pair_decode_root {L : Type*} [Field L] [CharZero L]
    (φ : Coefficient →+* L) (p q : Polynomial Coefficient) (c : ℕ) (theta : L)
    (hpd : (p.map φ).natDegree = p.natDegree) (hqd : (q.map φ).natDegree = q.natDegree)
    (hp : (p.map φ).Separable) (hq : (q.map φ).Separable)
    (hs : ((cannyResultant p q c).map φ).Separable)
    (ht : (cannyResultant p q c).eval₂ φ theta = 0) :
    p.eval₂ φ (pairCoordinates φ p q c theta).1 = 0 ∧
      q.eval₂ φ (pairCoordinates φ p q c theta).2 = 0 ∧
      shear c (pairCoordinates φ p q c theta) = theta ∧
      (PrimitivePair.denominator p q c).eval₂ φ theta ≠ 0 := by
  have hm := resultant_map_of_degrees φ p q c hpd hqd
  rw [hm] at hs
  have ht' : (cannyResultant (p.map φ) (q.map φ) c).eval theta = 0 := by
    rw [← hm, Polynomial.eval_map]
    exact ht
  have hr := field_decode_root _ _ c theta hp hq hs ht'
  rw [← pairCoordinates_eq φ p q c theta hpd hqd] at hr
  simpa only [Polynomial.eval_map, ← denominator_map_of_degrees φ p q c hpd hqd] using hr

noncomputable def pairCoordinate (right : Bool) (p q : Polynomial Coefficient) (c : ℕ) : Coordinate :=
  ⟨if right then PrimitivePair.rightNumerator p q c else PrimitivePair.leftNumerator p q c,
    PrimitivePair.denominator p q c⟩

theorem eval_pairCoordinate_false {L : Type*} [Field L] (φ : Coefficient →+* L)
    (p q : Polynomial Coefficient) (c : ℕ) (theta : L) :
    (pairCoordinate false p q c).eval φ theta = (pairCoordinates φ p q c theta).1 := rfl

theorem eval_pairCoordinate_true {L : Type*} [Field L] (φ : Coefficient →+* L)
    (p q : Polynomial Coefficient) (c : ℕ) (theta : L) :
    (pairCoordinate true p q c).eval φ theta = (pairCoordinates φ p q c theta).2 := rfl

noncomputable def coordinate (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → Coordinate
  | 0, _, _ => SymbolicBalancedCoordinate.identity
  | h + 1, i, j => if j < 2 ^ h then
      (coordinate a c h (2 * i) j).comp (pairCoordinate false (node a c h (2 * i)) (node a c h (2 * i + 1)) (c h i))
    else (coordinate a c h (2 * i + 1) (j - 2 ^ h)).comp
      (pairCoordinate true (node a c h (2 * i)) (node a c h (2 * i + 1)) (c h i))

/-- The coordinate decoding induction depends only on the composition laws.
Both minimal-degree and public-envelope clearing instantiate this theorem while
retaining their own literal numerator and denominator polynomials. -/
theorem coordinate_spec_of_composition
    (C : ℕ → ℕ → ℕ → Coordinate) (compose : ℕ → Coordinate → Coordinate → Coordinate)
    (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ)
    (hzero : ∀ i j, C 0 i j = SymbolicBalancedCoordinate.identity)
    (hstep : ∀ h i j, C (h + 1) i j = if j < 2 ^ h then
      compose h (C h (2 * i) j)
        (pairCoordinate false (node a c h (2 * i)) (node a c h (2 * i + 1)) (c h i))
      else compose h (C h (2 * i + 1) (j - 2 ^ h))
        (pairCoordinate true (node a c h (2 * i)) (node a c h (2 * i + 1)) (c h i)))
    (B : Budget) (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c)
    (height : ℕ) (hs : SeparableTable a c height) (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic (referenceExponent B height))
    (hcompose : ∀ h i j (inner : Coordinate) (theta : ℝ),
      inner.denominator.eval₂ (scalarEvaluation beta) theta ≠ 0 →
      (C h i j).denominator.eval₂ (scalarEvaluation beta) (inner.eval (scalarEvaluation beta) theta) ≠ 0 →
      (compose h (C h i j) inner).denominator.eval₂ (scalarEvaluation beta) theta ≠ 0 ∧
        (compose h (C h i j) inner).eval (scalarEvaluation beta) theta =
          (C h i j).eval (scalarEvaluation beta) (inner.eval (scalarEvaluation beta) theta))
    (h i j : ℕ) (hh : h ≤ height) (hj : j < 2 ^ h) (theta : ℝ)
    (ht : (node a c h i).eval₂ (scalarEvaluation beta) theta = 0) :
    (C h i j).denominator.eval₂ (scalarEvaluation beta) theta ≠ 0 ∧
      (C h i j).eval (scalarEvaluation beta) theta =
        BalancedPrimitiveTree.coordinate h (decode a c beta h i theta) j := by
  induction h generalizing i j theta with
  | zero => simp only [hzero, SymbolicBalancedCoordinate.identity, Polynomial.eval₂_one,
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
      simp only [hstep, ite_eq_left hjl]
      have hn := hcompose h (2 * i) j _ theta hd hl.1
      refine ⟨hn.1, hn.2.trans ?_⟩
      simpa only [decode, BalancedPrimitiveTree.coordinate, ite_eq_left hjl, eval_pairCoordinate_false] using hl.2
    · have hjr : j - 2 ^ h < 2 ^ h := by rw [pow_succ] at hj; omega
      have hr' := ih (2 * i + 1) (j - 2 ^ h) (by omega) hjr _ hr.2.1
      have hd : (pairCoordinate true (node a c h (2 * i)) (node a c h (2 * i + 1)) (c h i)).denominator.eval₂
          (scalarEvaluation beta) theta ≠ 0 := hr.2.2.2
      simp only [hstep, ite_eq_right hjl]
      have hn := hcompose h (2 * i + 1) (j - 2 ^ h) _ theta hd hr'.1
      refine ⟨hn.1, hn.2.trans ?_⟩
      simpa only [decode, BalancedPrimitiveTree.coordinate, ite_eq_right hjl, eval_pairCoordinate_true] using hr'.2

theorem coordinate_spec (B : Budget) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ)
    (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c) (height : ℕ) (hs : SeparableTable a c height)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (referenceExponent B height))
    (h i j : ℕ) (hh : h ≤ height) (hj : j < 2 ^ h) (theta : ℝ)
    (ht : (node a c h i).eval₂ (scalarEvaluation beta) theta = 0) :
    (coordinate a c h i j).denominator.eval₂ (scalarEvaluation beta) theta ≠ 0 ∧
      (coordinate a c h i j).eval (scalarEvaluation beta) theta =
        BalancedPrimitiveTree.coordinate h (decode a c beta h i theta) j := by
  exact coordinate_spec_of_composition (coordinate a c) (fun _ => Coordinate.comp) a c
    (fun _ _ => rfl) (fun _ _ _ => rfl) B ha hc height hs beta hb he
    (fun _ _ _ inner theta hi ho =>
      ⟨Coordinate.comp_denominator_ne_zero _ inner _ theta hi ho, Coordinate.eval_comp _ inner _ theta hi⟩)
    h i j hh hj theta ht

namespace Reference

noncomputable def coordinate {B : Budget} {height : ℕ} (R : Reference B height)
    (a : ℕ → Polynomial Coefficient) (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0)
    (h i j : ℕ) : Coordinate :=
  SymbolicFixedTable.coordinate (fun i => SymbolicScaledSquarefree.polynomial (a i)) (R.directions a ha hn) h i j

theorem coordinate_spec {B : Budget} {height : ℕ} (R : Reference B height)
    (a : ℕ → Polynomial Coefficient) (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic R.exponent)
    (h i j : ℕ) (hh : h ≤ height) (hj : j < 2 ^ h) (theta : ℝ)
    (ht : (node (fun i => SymbolicScaledSquarefree.polynomial (a i)) (R.directions a ha hn) h i).eval₂
      (scalarEvaluation beta) theta = 0) :
    (R.coordinate a ha hn h i j).denominator.eval₂ (scalarEvaluation beta) theta ≠ 0 ∧
      (R.coordinate a ha hn h i j).eval (scalarEvaluation beta) theta =
        BalancedPrimitiveTree.coordinate h
          (decode (fun i => SymbolicScaledSquarefree.polynomial (a i)) (R.directions a ha hn) beta h i theta) j :=
  SymbolicFixedTable.coordinate_spec B.squarefree _ _ (fun i => B.squarefree_controls _ (ha i))
    (R.admissible a ha hn) height (R.separableTable a ha hn) beta hb
    (he.trans (dyadic_antitone R.tree_sufficient)) h i j hh hj theta ht

theorem coordinate_encode {B : Budget} {height : ℕ} (R : Reference B height)
    (a : ℕ → Polynomial Coefficient) (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic R.exponent)
    (h i j : ℕ) (hh : h ≤ height) (hj : j < 2 ^ h) (x : Values ℝ h) (hx : valid a beta h i x) :
    (R.coordinate a ha hn h i j).eval (scalarEvaluation beta) (encode (R.directions a ha hn) h i x) =
      BalancedPrimitiveTree.coordinate h x j := by
  have hvalid := (valid_squarefree_iff B a ha hn beta hb (he.trans (dyadic_antitone R.leaf_sufficient)) h i x).mpr hx
  have ht := encode_valid B.squarefree _ _ (fun i => B.squarefree_controls _ (ha i))
    (R.admissible a ha hn) height (R.separableTable a ha hn) beta hb
    (he.trans (dyadic_antitone R.tree_sufficient)) h i hh x hvalid
  have hs := (R.coordinate_spec a ha hn beta hb he h i j hh hj _ ht.1).2
  rw [ht.2] at hs
  exact hs

end Reference

end LeanCanny.Algebra.SymbolicFixedTable

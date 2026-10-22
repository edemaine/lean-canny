/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableCoordinates

/-! # A finite symbolic family prepared by the existing integer search

Original nonzero bivariate leaves are padded with X, prepared at one explicit
source reference, and represented by an actual symbolic parameter and rational
coordinates. All smaller positive evaluations preserve the full original
Cartesian root set, including count zero.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTable
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open BalancedPrimitiveTree (coordinate)
open scoped Classical

theorem valid_iff (a : ℕ → Polynomial Coefficient) (beta : ℝ) (h i : ℕ) (x : Values ℝ h) :
    valid a beta h i x ↔ ∀ j < 2 ^ h,
      (a (2 ^ h * i + j)).eval₂ (scalarEvaluation beta) (BalancedPrimitiveTree.coordinate h x j) = 0 := by
  induction h generalizing i with
  | zero =>
    constructor
    · intro hx j hj
      have hj' : j = 0 := by simp only [pow_zero] at hj; omega
      simpa only [pow_zero, one_mul, hj', Nat.add_zero, BalancedPrimitiveTree.coordinate, valid] using hx
    · intro hx
      simpa only [pow_zero, one_mul, Nat.add_zero, BalancedPrimitiveTree.coordinate, valid] using hx 0 (by decide)
  | succ h ih =>
    have hlbase : 2 ^ h * (2 * i) = 2 ^ (h + 1) * i := by rw [pow_succ]; ring
    have hrbase : 2 ^ h * (2 * i + 1) = 2 ^ (h + 1) * i + 2 ^ h := by rw [pow_succ]; ring
    rw [valid, ih, ih]
    constructor
    · rintro ⟨hl, hr⟩ j hj
      by_cases hjl : j < 2 ^ h
      · simpa only [BalancedPrimitiveTree.coordinate, ite_eq_left hjl, hlbase] using hl j hjl
      · have hjr : j - 2 ^ h < 2 ^ h := by rw [pow_succ] at hj; omega
        have haddr : 2 ^ h * (2 * i + 1) + (j - 2 ^ h) = 2 ^ (h + 1) * i + j := by rw [hrbase]; omega
        simpa only [BalancedPrimitiveTree.coordinate, ite_eq_right hjl, haddr] using hr (j - 2 ^ h) hjr
    · intro hx
      constructor
      · intro j hj
        have hj' : j < 2 ^ (h + 1) := by rw [pow_succ]; omega
        simpa only [BalancedPrimitiveTree.coordinate, ite_eq_left hj, hlbase] using hx j hj'
      · intro j hj
        have hj' : 2 ^ h + j < 2 ^ (h + 1) := by rw [pow_succ]; omega
        have hjn : ¬ 2 ^ h + j < 2 ^ h := by omega
        have haddr : 2 ^ (h + 1) * i + (2 ^ h + j) = 2 ^ h * (2 * i + 1) + j := by rw [hrbase]; omega
        simpa only [BalancedPrimitiveTree.coordinate, ite_eq_right hjn, Nat.add_sub_cancel_left, haddr] using hx (2 ^ h + j) hj'

end LeanCanny.Algebra.SymbolicFixedTable

namespace LeanCanny.Algebra.SymbolicFixedTableFinite
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open SymbolicFixedTable (Budget Reference Values)
open BalancedPrimitiveTree (coordinate tabulate coordinate_tabulate coordinate_injective)
open scoped Classical

structure Family where
  count : ℕ
  polynomial : ℕ → Polynomial Coefficient
  budget : Budget
  controls : ∀ i < count, budget.Controls (polynomial i)
  nonzero : ∀ i < count, polynomial i ≠ 0

namespace Family

def paddedBudget (F : Family) : Budget := ⟨F.budget.degree + 1, F.budget.innerDegree, F.budget.massExponent⟩

noncomputable def padded (F : Family) (i : ℕ) : Polynomial Coefficient :=
  if i < F.count then F.polynomial i else X

theorem padded_nonzero (F : Family) (i : ℕ) : F.padded i ≠ 0 := by
  by_cases hi : i < F.count
  · exact (ite_eq_left hi ▸ F.nonzero i hi : (if i < F.count then F.polynomial i else X) ≠ 0)
  · simpa only [padded, ite_eq_right hi] using (Polynomial.X_ne_zero (R := Coefficient))

theorem padded_controls (F : Family) (i : ℕ) : F.paddedBudget.Controls (F.padded i) := by
  by_cases hi : i < F.count
  · rw [padded, ite_eq_left hi]
    have h := F.controls i hi
    exact ⟨h.1.trans (Nat.le_succ _), h.2⟩
  · rw [padded, ite_eq_right hi]
    refine ⟨by simp only [natDegree_X]; exact Nat.le_add_left 1 _, ?_, ?_⟩
    · intro k
      simp only [coeff_X]
      split_ifs <;> simp
    · intro k
      simp only [coeff_X]
      split_ifs
      · have h1 : coefficientMass (1 : ℤ[X]) = 1 := by
          simpa only [Polynomial.C_1, Int.natAbs_one] using coefficientMass_C (1 : ℤ)
        rw [h1]
        exact Nat.one_le_two_pow
      · simp

def reference (F : Family) : Reference F.paddedBudget F.count.size :=
  SymbolicFixedTable.sourceReference F.paddedBudget F.count

def exponent (F : Family) : ℕ := F.reference.exponent

theorem exponent_eq (F : Family) : F.exponent = SymbolicFixedTable.sourceExponent
    (F.budget.degree + 1) F.budget.innerDegree F.budget.massExponent F.count := rfl

noncomputable def directions (F : Family) : ℕ → ℕ → ℕ := F.reference.directions F.padded F.padded_controls F.padded_nonzero

noncomputable def parameter (F : Family) : Polynomial Coefficient :=
  SymbolicFixedTable.node (fun i => SymbolicScaledSquarefree.polynomial (F.padded i)) F.directions F.count.size 0

noncomputable def coordinate (F : Family) (i : Fin F.count) : SymbolicBalancedCoordinate.Coordinate :=
  F.reference.coordinate F.padded F.padded_controls F.padded_nonzero F.count.size 0 i.val

noncomputable def decodedValues (F : Family) (beta theta : ℝ) : Values ℝ F.count.size :=
  SymbolicFixedTable.decode (fun i => SymbolicScaledSquarefree.polynomial (F.padded i)) F.directions beta F.count.size 0 theta

noncomputable def decode (F : Family) (beta theta : ℝ) : Fin F.count → ℝ :=
  fun i => BalancedPrimitiveTree.coordinate F.count.size (F.decodedValues beta theta) i.val

def paddedValues (F : Family) (x : Fin F.count → ℝ) : Values ℝ F.count.size :=
  tabulate F.count.size (fun j => if hj : j < F.count then x ⟨j, hj⟩ else 0)

noncomputable def encode (F : Family) (x : Fin F.count → ℝ) : ℝ :=
  SymbolicFixedTable.encode F.directions F.count.size 0 (F.paddedValues x)

theorem decoded_valid (F : Family) (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic F.exponent) (theta : ℝ)
    (ht : F.parameter.eval₂ (scalarEvaluation beta) theta = 0) :
    SymbolicFixedTable.valid F.padded beta F.count.size 0 (F.decodedValues beta theta) :=
  ((F.reference.rootEquiv F.padded F.padded_controls F.padded_nonzero beta hb he
    F.count.size 0 le_rfl) ⟨theta, ht⟩).property

theorem decode_root (F : Family) (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic F.exponent) (theta : ℝ)
    (ht : F.parameter.eval₂ (scalarEvaluation beta) theta = 0) (i : Fin F.count) :
    (F.polynomial i.val).eval₂ (scalarEvaluation beta) (F.decode beta theta i) = 0 := by
  have h := (SymbolicFixedTable.valid_iff F.padded beta F.count.size 0 _).mp
    (F.decoded_valid beta hb he theta ht) i.val (i.isLt.trans (Nat.lt_size_self _))
  simpa only [Nat.mul_zero, Nat.zero_add, padded, ite_eq_left i.isLt, decode] using h

theorem paddedValues_valid (F : Family) (beta : ℝ) (x : Fin F.count → ℝ)
    (hx : ∀ i, (F.polynomial i.val).eval₂ (scalarEvaluation beta) (x i) = 0) :
    SymbolicFixedTable.valid F.padded beta F.count.size 0 (F.paddedValues x) := by
  rw [SymbolicFixedTable.valid_iff]
  intro j hj
  simp only [Nat.mul_zero, Nat.zero_add, paddedValues, coordinate_tabulate _ _ j hj]
  by_cases hjn : j < F.count
  · simpa only [dite_eq_left hjn, padded, ite_eq_left hjn] using hx ⟨j, hjn⟩
  · simp only [dite_eq_right hjn, padded, ite_eq_right hjn, Polynomial.eval₂_X]

theorem encode_roots (F : Family) (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic F.exponent) (x : Fin F.count → ℝ)
    (hx : ∀ i, (F.polynomial i.val).eval₂ (scalarEvaluation beta) (x i) = 0) :
    F.parameter.eval₂ (scalarEvaluation beta) (F.encode x) = 0 ∧ F.decode beta (F.encode x) = x := by
  have hv := (SymbolicFixedTable.valid_squarefree_iff F.paddedBudget F.padded F.padded_controls F.padded_nonzero
    beta hb (he.trans (SymbolicPrimitivePair.dyadic_antitone F.reference.leaf_sufficient))
    F.count.size 0 (F.paddedValues x)).mpr (F.paddedValues_valid beta x hx)
  have ht := SymbolicFixedTable.encode_valid F.paddedBudget.squarefree
    (fun i => SymbolicScaledSquarefree.polynomial (F.padded i)) F.directions
    (fun i => F.paddedBudget.squarefree_controls _ (F.padded_controls i)) (F.reference.admissible F.padded F.padded_controls F.padded_nonzero)
    F.count.size (F.reference.separableTable F.padded F.padded_controls F.padded_nonzero) beta hb
    (he.trans (SymbolicPrimitivePair.dyadic_antitone F.reference.tree_sufficient)) F.count.size 0 le_rfl _ hv
  refine ⟨ht.1, ?_⟩
  funext i
  change BalancedPrimitiveTree.coordinate F.count.size
    (SymbolicFixedTable.decode (fun i => SymbolicScaledSquarefree.polynomial (F.padded i)) F.directions beta F.count.size 0
      (SymbolicFixedTable.encode F.directions F.count.size 0 (F.paddedValues x))) i.val = x i
  rw [ht.2, paddedValues, coordinate_tabulate _ _ i.val (i.isLt.trans (Nat.lt_size_self _)), dite_eq_left i.isLt]

theorem encode_decode (F : Family) (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic F.exponent) (theta : ℝ)
    (ht : F.parameter.eval₂ (scalarEvaluation beta) theta = 0) : F.encode (F.decode beta theta) = theta := by
  have hr := SymbolicFixedTable.decode_root F.paddedBudget.squarefree
    (fun i => SymbolicScaledSquarefree.polynomial (F.padded i)) F.directions
    (fun i => F.paddedBudget.squarefree_controls _ (F.padded_controls i)) (F.reference.admissible F.padded F.padded_controls F.padded_nonzero)
    F.count.size (F.reference.separableTable F.padded F.padded_controls F.padded_nonzero) beta hb
    (he.trans (SymbolicPrimitivePair.dyadic_antitone F.reference.tree_sufficient)) F.count.size 0 le_rfl theta ht
  have hv : F.paddedValues (F.decode beta theta) = F.decodedValues beta theta := by
    apply coordinate_injective
    intro j hj
    rw [paddedValues, coordinate_tabulate _ _ j hj]
    by_cases hjn : j < F.count
    · rw [dite_eq_left hjn]; rfl
    · rw [dite_eq_right hjn]
      have h := (SymbolicFixedTable.valid_iff F.padded beta F.count.size 0 _).mp
        (F.decoded_valid beta hb he theta ht) j hj
      simp only [Nat.mul_zero, Nat.zero_add, padded, ite_eq_right hjn, Polynomial.eval₂_X] at h
      exact h.symm
  change SymbolicFixedTable.encode F.directions F.count.size 0 (F.paddedValues (F.decode beta theta)) = theta
  rw [hv]
  exact hr.2

noncomputable def rootEquiv (F : Family) (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic F.exponent) :
    {theta : ℝ // F.parameter.eval₂ (scalarEvaluation beta) theta = 0} ≃
      {x : Fin F.count → ℝ // ∀ i, (F.polynomial i.val).eval₂ (scalarEvaluation beta) (x i) = 0} where
  toFun theta := ⟨F.decode beta theta.val, F.decode_root beta hb he theta.val theta.property⟩
  invFun x := ⟨F.encode x.val, (F.encode_roots beta hb he x.val x.property).1⟩
  left_inv theta := Subtype.ext (F.encode_decode beta hb he theta.val theta.property)
  right_inv x := Subtype.ext (F.encode_roots beta hb he x.val x.property).2

theorem coordinate_spec (F : Family) (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic F.exponent) (theta : ℝ)
    (ht : F.parameter.eval₂ (scalarEvaluation beta) theta = 0) (i : Fin F.count) :
    (F.coordinate i).denominator.eval₂ (scalarEvaluation beta) theta ≠ 0 ∧
      (F.coordinate i).eval (scalarEvaluation beta) theta = F.decode beta theta i :=
  F.reference.coordinate_spec F.padded F.padded_controls F.padded_nonzero beta hb he F.count.size 0 i.val le_rfl (i.isLt.trans (Nat.lt_size_self _)) theta ht

theorem coordinate_root (F : Family) (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic F.exponent) (theta : ℝ)
    (ht : F.parameter.eval₂ (scalarEvaluation beta) theta = 0) (i : Fin F.count) :
    (F.polynomial i.val).eval₂ (scalarEvaluation beta) ((F.coordinate i).eval (scalarEvaluation beta) theta) = 0 := by
  rw [(F.coordinate_spec beta hb he theta ht i).2]
  exact F.decode_root beta hb he theta ht i

theorem coordinates_encode (F : Family) (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic F.exponent) (x : Fin F.count → ℝ)
    (hx : ∀ i, (F.polynomial i.val).eval₂ (scalarEvaluation beta) (x i) = 0) (i : Fin F.count) :
    (F.coordinate i).eval (scalarEvaluation beta) (F.encode x) = x i := by
  have ht := F.encode_roots beta hb he x hx
  rw [(F.coordinate_spec beta hb he _ ht.1 i).2, ht.2]

end Family

end LeanCanny.Algebra.SymbolicFixedTableFinite

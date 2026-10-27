/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBlockSource

/-! # Uniform native widths for sample coordinate blocks

The parameter occupies the lowest exponent block. Each free coordinate
occupies one further block. The block width and the total serialized exponent
width have unary polynomial-time controls, even when polynomial degrees are
large binary numbers.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleBlockEncoding
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial Brackets
open BoundedCriticalSampleBlockSource
open scoped Classical
attribute [local irreducible] BoundedCriticalRationalCoordinates.coordinateDegree
  BoundedCriticalRationalCoordinates.coordinateMass

noncomputable def source (read : List Bool → List Bool) : RationalSubstitutionBits.Source :=
  RationalSubstitutionBits.Source.ofTerm read
noncomputable def extent (P : Readers) (u : List Bool) : ℕ := max (BoundedCriticalRationalCoordinates.coordinateDegree P (pairFst u)) 1
noncomputable def budget (P : Readers) (read : List Bool → List Bool) (u : List Bool) : ℕ :=
  (BivariateRationalTermReader.weight (source read) u + 1) * extent P u + 1
noncomputable def width (P : Readers) (read : List Bool → List Bool) (u : List Bool) : ℕ := (budget P read u).size
noncomputable def span (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (u : List Bool) : ℕ :=
  width P read u * (k u + 1)

theorem extent_binary {P : Readers} (h : P.PolyTime) : BinaryFn (extent P) :=
  BivariateRationalTermReader.max_binary ((BoundedCriticalRationalCoordinates.coordinateDegree_binary h).comp pairFst_mem_FP) (BinaryFn.const 1)
theorem budget_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) : BinaryFn (budget P read) :=
  (((BivariateRationalTermReader.weight_binary (source read) (RationalSubstitutionBits.Source.ofTerm_polyTime hr)).add
    (BinaryFn.const 1)).mul (extent_binary h)).add (BinaryFn.const 1)
theorem width_unary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) : UnaryFn (width P read) :=
  (UnaryFn.length (budget_binary h read hr).bits_mem_FP).of_eq (fun u => by
    simp only [BinaryNatCode.encode, width, Nat.size_eq_bits_len])
theorem span_unary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k : List Bool → ℕ} (hk : UnaryFn k) : UnaryFn (span P read k) :=
  (width_unary h read hr).mul (hk.add (UnaryFn.const 1))

theorem extent_lt (P : Readers) (read : List Bool → List Bool) (u : List Bool) : extent P u < 2 ^ width P read u := by
  have h : extent P u ≤ (BivariateRationalTermReader.weight (source read) u + 1) * extent P u := Nat.le_mul_of_pos_left _ (by omega)
  exact (by unfold budget; omega : extent P u ≤ budget P read u).trans_lt (Nat.lt_size_self _)
theorem clearing_lt (P : Readers) (read : List Bool → List Bool) (u : List Bool) :
    BivariateRationalTermReader.weight (source read) u * extent P u < 2 ^ width P read u := by
  have h := Nat.lt_size_self (budget P read u)
  have hb : BivariateRationalTermReader.weight (source read) u * extent P u ≤ budget P read u := by
    unfold budget
    nlinarith
  exact hb.trans_lt h

noncomputable def power (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (u : List Bool) (i : ℕ) : ℕ :=
  2 ^ ((min (i - o u) (k u) + 1) * width P read u)
noncomputable def encoded (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (b : Bool) (u : List Bool) (i : ℕ) : ℤ[X] :=
  if InBlock (o u) (k u) i then if b then X ^ power P read o k u i else 1
  else BoundedCriticalSampleLineCoordinates.base P b u i

theorem encode_coordinate (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (b : Bool) (u : List Bool) (i : ℕ) :
    FixedWidthKronecker.encode (k u + 1) (width P read u) (coordinate P o k b u i) = encoded P read o k b u i := by
  by_cases hi : InBlock (o u) (k u) i
  · have hm : min (i - o u) (k u) = i - o u := Nat.min_eq_left (by unfold InBlock at hi; omega)
    cases b
    · simp only [coordinate, encoded, hi, dite_true, ite_true, Bool.false_eq_true, ite_false, map_one]
    · simp only [coordinate, encoded, hi, dite_true, ite_true, FixedWidthKronecker.encode,
        MvPolynomial.eval₂Hom_X', freeVariable, power, hm]
  · simp only [coordinate, encoded, hi, dite_false, ite_false, IndexedMultivariateRational.encode_parameter]

theorem encoded_mass (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (b : Bool) (u : List Bool) (i : ℕ) :
    coefficientMass (encoded P read o k b u i) ≤ 2 ^ BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u) := by
  unfold encoded
  split_ifs
  · rw [coefficientMass_X_pow]
    exact Nat.one_le_two_pow
  · simpa only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one] using
      (Nat.one_le_two_pow : 1 ≤ 2 ^ BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u))
  · exact BoundedCriticalSampleLineCoordinates.base_mass P b u i

theorem encoded_degree (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (b : Bool) (u : List Bool) (i : ℕ) : (encoded P read o k b u i).natDegree ≤ 2 ^ span P read k u := by
  unfold encoded
  split_ifs
  · rw [natDegree_X_pow]
    apply Nat.pow_le_pow_right (by decide)
    unfold span
    nlinarith [Nat.min_le_right (i - o u) (k u)]
  · simp only [natDegree_one, Nat.zero_le]
  · apply (BoundedCriticalSampleLineCoordinates.base_degree P b u i).trans
    apply (Nat.le_max_left _ _).trans
    apply (extent_lt P read u).le.trans
    apply Nat.pow_le_pow_right (by decide)
    unfold span
    nlinarith

end LeanCanny.Encoding.BoundedCriticalSampleBlockEncoding

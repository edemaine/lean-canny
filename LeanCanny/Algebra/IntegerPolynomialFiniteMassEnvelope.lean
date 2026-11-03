/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace
public import LeanCanny.Computation.WordResourceEnvelope
/-! # An original-only uniform mass ceiling for a finite source bank -/
@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialFiniteMassEnvelope
open LeanCanny.Encoding LeanCanny.Computation

def lengthBound (count : List Bool → ℕ) (root : List Bool) := 2*root.length+2+count root
theorem lengthBound_unary {count : List Bool → ℕ} (hc : UnaryFn count) : UnaryFn (lengthBound count) :=
  (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 2)).add hc

noncomputable def height (S : IntegerPolynomialRootQueriesBits.Source) (hS : IntegerPolynomialRootQueriesBits.Access S)
    (count : List Bool → ℕ) (hc : UnaryFn count) :=
  Classical.choose (hS.mass.wordEnvelope (lengthBound_unary hc))

theorem height_binary (S : IntegerPolynomialRootQueriesBits.Source) (hS : IntegerPolynomialRootQueriesBits.Access S)
    (count : List Bool → ℕ) (hc : UnaryFn count) : BinaryFn (height S hS count hc) :=
  (Classical.choose_spec (hS.mass.wordEnvelope (lengthBound_unary hc))).1

theorem mass_le (S : IntegerPolynomialRootQueriesBits.Source) (hS : IntegerPolynomialRootQueriesBits.Access S)
    (count : List Bool → ℕ) (hc : UnaryFn count) (root : List Bool) (i : ℕ) (hi : i<count root) :
    S.mass (pair root (BinaryNatCode.encode i))≤height S hS count hc root := by
  apply (Classical.choose_spec (hS.mass.wordEnvelope (lengthBound_unary hc))).2
  rw [pair_length,BinaryNatCode.length_encode]
  have H := Nat.size_le_self i
  unfold lengthBound
  omega

theorem coefficient_le (S : IntegerPolynomialRootQueriesBits.Source) (hS : IntegerPolynomialRootQueriesBits.Access S)
    (count : List Bool → ℕ) (hc : UnaryFn count) (root : List Bool) (i k : ℕ) (hi : i<count root) :
    ((S.polynomial (pair root (BinaryNatCode.encode i))).coeff k).natAbs≤2^(height S hS count hc root) :=
  ((coeff_natAbs_le_coefficientMass _ k).trans (S.mass_bound _)).trans
    (Nat.pow_le_pow_right (by decide) (mass_le S hS count hc root i hi))

end LeanCanny.Algebra.IntegerPolynomialFiniteMassEnvelope

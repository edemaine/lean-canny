/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.FormulaAtomPolynomials
public import LeanCanny.ETR.BivariateRationalTermReader

/-! # Native formula atoms in rational bivariate coordinates

Each preserved arithmetic term is cleared with a fixed even power of every
coordinate denominator. A uniform formula-size allowance bounds all slots.
The coefficient readers retain the original numerator and denominator sources.
-/

@[expose] public section
namespace LeanCanny.ETR.FormulaRationalAtoms
open Polynomial LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open FormulaBooleanCircuitSource FormulaAtomPolynomials
open scoped Classical

attribute [local irreducible] circuit termOfReader termCode readerQuery

theorem source_syntax (read : List Bool → List Bool) (w : List Bool) :
    (termSource read).syntax w = termOfReader read w := by
  unfold termSource RationalSubstitutionBits.Source.syntax RationalSubstitutionBits.Source.ofTerm termOfReader term
  rfl

theorem source_arity (read : List Bool → List Bool) (w : List Bool) :
    Nat.fromBitsLE ((termSource read).arity w) = (termOfReader read w).toData.size := by
  simp only [termSource, RationalSubstitutionBits.Source.ofTerm, TermView.normalize_eq_term, Data.length_toBits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Function.comp_apply, termOfReader, term]

theorem source_weight (read : List Bool → List Bool) (w : List Bool) :
    BivariateRationalTermReader.weight (termSource read) w = 2 * (termOfReader read w).toData.size ^ 2 := by
  rw [BivariateRationalTermReader.weight, source_arity, BivariateTermReader.size_eq, source_syntax]
  ring

def clearingBudget (read : List Bool → List Bool) (c : List Bool) : ℕ := 2 * budget read c ^ 2

theorem clearingBudget_binary (read : List Bool → List Bool) (hr : read ∈ FP) : BinaryFn (clearingBudget read) := by
  have H := (BinaryFn.const 2).mul ((budget_binary read hr).mul (budget_binary read hr))
  exact H.of_eq (fun _ => by simp only [clearingBudget, pow_two])

theorem weight_le (read : List Bool → List Bool) (c : List Bool) (i : ℕ) :
    BivariateRationalTermReader.weight (termSource read) (pair c (BinaryNatCode.encode i)) ≤ clearingBudget read c := by
  rw [source_weight]
  exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (term_size_le read c i) 2)

noncomputable def atomPolynomial (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family)
    (c : List Bool) (i : ℕ) : (ℤ[X])[X] :=
  BivariateRationalTermReader.polynomial (termSource read) (N.comp pairFst) (D.comp pairFst) (pair c (BinaryNatCode.encode i))

theorem polynomial_indexed (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family) (w : List Bool) :
    BivariateRationalTermReader.polynomial (termSource read) (N.comp pairFst) (D.comp pairFst) w =
      atomPolynomial read N D (pairFst w) (Nat.fromBitsLE (pairSnd w)) := by
  simp only [atomPolynomial, BivariateRationalTermReader.polynomial, source_syntax, source_arity,
    BivariateQueryProductBits.Family.comp, pairFst_pair]
  rw [term_canonical read w]

noncomputable def family (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family) :
    BivariateQueryProductBits.Family where
  polynomial := atomPolynomial read N D
  exponent _ _ := 1
  count c := circuit.count (read c)
  degree c := clearingBudget read c * max (N.degree c) (D.degree c)
  parameterDegree c := clearingBudget read c * max (N.parameterDegree c) (D.parameterDegree c)
  mass c := 2 * budget read c + 1 + clearingBudget read c * BivariateRationalTermReader.coordinateMass N D c
  polynomial_degree c i := by
    have H := BivariateRationalTermReader.outer_degree_le (termSource read) (N.comp pairFst) (D.comp pairFst)
      (pair c (BinaryNatCode.encode i))
    simp only [BivariateQueryProductBits.Family.comp, pairFst_pair] at H
    exact H.trans (Nat.mul_le_mul_right _ (weight_le read c i))
  coefficient_degree c i j := by
    have H := BivariateRationalTermReader.inner_degree_le (termSource read) (N.comp pairFst) (D.comp pairFst)
      (pair c (BinaryNatCode.encode i)) j
    simp only [BivariateQueryProductBits.Family.comp, pairFst_pair] at H
    exact H.trans (Nat.mul_le_mul_right _ (weight_le read c i))
  coefficient_mass c i j := by
    apply (NestedMass.coeff_le _ _).trans
    have H := BivariateRationalTermReader.mass_le (termSource read) (N.comp pairFst) (D.comp pairFst)
      (pair c (BinaryNatCode.encode i))
    apply H.trans
    apply Nat.pow_le_pow_right (by decide)
    simp only [source_syntax, BivariateRationalTermReader.coordinateMass, BivariateQueryProductBits.Family.comp,
      pairFst_pair]
    exact Nat.add_le_add (by have := term_size_le read c i; omega) (Nat.mul_le_mul_right _ (weight_le read c i))

attribute [local irreducible] termSource BivariateRationalTermReader.reader

noncomputable def access (read : List Bool → List Bool) (hr : read ∈ FP) {N D : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access N) (B : BivariateQueryProductBits.Access D) : BivariateQueryProductBits.Access (family read N D) where
  reader := {
    coefficient := (BivariateRationalTermReader.reader (termSource read) (termSource_polyTime read hr)
      (A.comp pairFst pairFst_mem_FP) (B.comp pairFst pairFst_mem_FP)).coefficient
    evaluator := (BivariateRationalTermReader.reader (termSource read) (termSource_polyTime read hr)
      (A.comp pairFst pairFst_mem_FP) (B.comp pairFst pairFst_mem_FP)).evaluator
    coefficient_eq q u v := by
      have H := (BivariateRationalTermReader.reader (termSource read) (termSource_polyTime read hr)
        (A.comp pairFst pairFst_mem_FP) (B.comp pairFst pairFst_mem_FP)).coefficient_eq q u v
      rw [polynomial_indexed] at H
      exact H }
  exponent := fun _ => BinaryNatCode.encode 1
  exponent_eq _ _ := rfl
  exponent_FP := constFn_mem_FP _
  count_binary := BinaryFn.ofUnary (circuit_access.comp read hr).count
  degree_binary := (clearingBudget_binary read hr).mul (BivariateRationalTermReader.max_binary A.degree_binary B.degree_binary)
  parameterDegree_binary := (clearingBudget_binary read hr).mul
    (BivariateRationalTermReader.max_binary A.parameterDegree_binary B.parameterDegree_binary)
  mass_binary := by
    have hn := A.mass_binary.add ((A.degree_binary.add (BinaryFn.const 1)).size)
    have hd := B.mass_binary.add ((B.degree_binary.add (BinaryFn.const 1)).size)
    exact (((BinaryFn.const 2).mul (budget_binary read hr)).add (BinaryFn.const 1)).add
      ((clearingBudget_binary read hr).mul (BivariateRationalTermReader.max_binary hn hd))

end LeanCanny.ETR.FormulaRationalAtoms

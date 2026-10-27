/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.FormulaBooleanCircuitSource
public import LeanCanny.ETR.BivariateTermReader
public import LeanCanny.Algebra.BivariateQueryReindex

/-! # Native atom polynomials for original formulas

Every circuit slot receives the polynomial obtained by evaluating its preserved
arithmetic term in the indexed bivariate coordinates. The literal formula size
bounds every slot, including unused positions and malformed term views.
-/

@[expose] public section
namespace LeanCanny.ETR.FormulaAtomPolynomials
open Polynomial LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open FormulaBooleanCircuitSource
open scoped Classical

attribute [local irreducible] circuit termOfReader termCode readerQuery

def budget (read : List Bool → List Bool) (c : List Bool) : ℕ := (FormulaView.normalize (read c)).length + 10

theorem budget_binary (read : List Bool → List Bool) (hr : read ∈ FP) : BinaryFn (budget read) :=
  (BinaryFn.ofUnary (UnaryFn.length (mem_FP_comp hr FormulaView.normalize_mem_FP))).add (BinaryFn.const 10)

theorem termCode_length_le (q : List Bool) : (termCode q).length ≤ (codes q).length := by
  simp only [termCode, arguments, node, Brackets.firstNode, Brackets.afterNode, Brackets.contents,
    List.length_take, List.length_drop]
  omega

theorem term_size_le (read : List Bool → List Bool) (c : List Bool) (i : ℕ) :
    (termOfReader read (pair c (BinaryNatCode.encode i))).toData.size ≤ budget read c := by
  have h := TermView.normalize_length_le (termCode (readerQuery read (pair c (BinaryNatCode.encode i))))
  rw [TermView.normalize_eq_term, Data.length_toBits] at h
  have H := termCode_length_le (readerQuery read (pair c (BinaryNatCode.encode i)))
  conv_rhs at H => simp only [codes, readerQuery, pairFst_pair]
  simpa only [termOfReader, term, budget] using h.trans (Nat.add_le_add_right H 10)

theorem term_canonical (read : List Bool → List Bool) (w : List Bool) :
    termOfReader read w = termOfReader read (pair (pairFst w) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd w)))) := by
  simp only [termOfReader, term, termCode, arguments, node, offset, codes, readerQuery,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def termSource (read : List Bool → List Bool) : RationalSubstitutionBits.Source :=
  RationalSubstitutionBits.Source.ofTerm (termCode ∘ readerQuery read)

theorem termSource_polyTime (read : List Bool → List Bool) (hr : read ∈ FP) : (termSource read).PolyTime :=
  RationalSubstitutionBits.Source.ofTerm_polyTime (termCodeOfReader_FP read hr)

noncomputable def family (read : List Bool → List Bool) (F : BivariateQueryProductBits.Family) :
    BivariateQueryProductBits.Family where
  polynomial c i := (termOfReader read (pair c (BinaryNatCode.encode i))).eval (F.polynomial c)
  exponent _ _ := 1
  count c := circuit.count (read c)
  degree c := budget read c * F.degree c
  parameterDegree c := budget read c * F.parameterDegree c
  mass c := budget read c * (F.mass c + (F.degree c + 1).size + 1)
  polynomial_degree c i := ((termOfReader read (pair c (BinaryNatCode.encode i))).eval_natDegree_le_size
    (F.polynomial c) _ (F.polynomial_degree c)).trans (Nat.mul_le_mul_right _ (term_size_le read c i))
  coefficient_degree c i j := ((termOfReader read (pair c (BinaryNatCode.encode i))).eval_innerDegree_le_size
    (F.polynomial c) _ (F.coefficient_degree c) j).trans (Nat.mul_le_mul_right _ (term_size_le read c i))
  coefficient_mass c i j := (NestedMass.coeff_le _ j).trans
    (((termOfReader read (pair c (BinaryNatCode.encode i))).eval_nestedMass_le_size (F.polynomial c)
      (F.mass c + (F.degree c + 1).size)
      (fun i => NestedMass.le_pow _ _ _ (F.polynomial_degree c i) (F.coefficient_mass c i))).trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (term_size_le read c i))))

theorem polynomial_indexed (read : List Bool → List Bool) (F : BivariateQueryProductBits.Family) (w : List Bool) :
    BivariateTermReader.polynomial (termSource read) (F.comp pairFst) w =
      (family read F).polynomial (pairFst w) (Nat.fromBitsLE (pairSnd w)) := by
  have ht : (termSource read).syntax w = termOfReader read w := by
    unfold termSource RationalSubstitutionBits.Source.syntax RationalSubstitutionBits.Source.ofTerm termOfReader term
    rfl
  simp only [BivariateTermReader.polynomial, BivariateQueryProductBits.Family.comp, ht]
  rw [term_canonical read w]
  rfl

attribute [local irreducible] termSource BivariateTermReader.reader

noncomputable def access (read : List Bool → List Bool) (hr : read ∈ FP) {F : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access F) : BivariateQueryProductBits.Access (family read F) where
  reader := {
    coefficient := (BivariateTermReader.reader (termSource read) (termSource_polyTime read hr) (A.comp pairFst pairFst_mem_FP)).coefficient
    evaluator := (BivariateTermReader.reader (termSource read) (termSource_polyTime read hr) (A.comp pairFst pairFst_mem_FP)).evaluator
    coefficient_eq q u v := by
      have H := (BivariateTermReader.reader (termSource read) (termSource_polyTime read hr)
        (A.comp pairFst pairFst_mem_FP)).coefficient_eq q u v
      rw [polynomial_indexed] at H
      exact H }
  exponent := fun _ => BinaryNatCode.encode 1
  exponent_eq _ _ := rfl
  exponent_FP := constFn_mem_FP _
  count_binary := BinaryFn.ofUnary (circuit_access.comp read hr).count
  degree_binary := (budget_binary read hr).mul A.degree_binary
  parameterDegree_binary := (budget_binary read hr).mul A.parameterDegree_binary
  mass_binary := by
    have hs : UnaryFn (fun c => (F.degree c + 1).size) :=
      (UnaryFn.length (A.degree_binary.add (BinaryFn.const 1)).bits_mem_FP).of_eq
        (fun c => BinaryNatCode.length_encode (F.degree c + 1))
    exact (budget_binary read hr).mul ((A.mass_binary.add (BinaryFn.ofUnary hs)).add (BinaryFn.const 1))

end LeanCanny.ETR.FormulaAtomPolynomials

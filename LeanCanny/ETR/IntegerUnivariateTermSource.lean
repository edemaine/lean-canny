/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.EncodedRationalSubstitution
public import LeanCanny.ETR.BivariateTermSubstitution
public import LeanCanny.Algebra.IndexedKroneckerReader
public import LeanCanny.Algebra.IntegerPolynomialDegreeSpace
public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace
/-! # Original univariate arithmetic words supply native integer readers

Variables in the original expression are interpreted as the one indeterminate.
The existing streamed substitution reader computes coefficients; exact degree
uses integer zero tests in space, with syntax-size degree and mass bounds.
-/
@[expose] public section
namespace LeanCanny.ETR.IntegerUnivariateTermSource
open Polynomial LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra MatrixPower
open RationalSubstitutionBits
open scoped Classical

def variableValue (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (IndexedKroneckerReader.degreeWord z)=1
  then ArithmeticBits.one (BinaryNat.succ (pairSnd z)) else []

theorem variableValue_FP : variableValue∈FP := by
  have HM : (fun z => BinaryNat.succ (pairSnd z))∈FP := mem_FP_comp (f := pairSnd) (g := BinaryNat.succ) pairSnd_mem_FP BinaryNat.succ_mem_FP
  have HO : (fun z => ArithmeticBits.one (BinaryNat.succ (pairSnd z)))∈FP := mem_FP_comp (f := fun z => BinaryNat.succ (pairSnd z)) (g := ArithmeticBits.one) HM ArithmeticBits.one_mem_FP
  exact ((BinaryFn.fromBits IndexedKroneckerReader.degreeWord_FP).eq (BinaryFn.const 1)).ite_mem_FP HO (constFn_mem_FP [])

theorem variable_packet (c : List Bool) (i k m : ℕ) (hm : 0<m) :
    variableValue (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m-1)))=
      residueBits (((X : ℤ[X]).coeff k : ℤ) : ZMod m) := by
  simp only [variableValue,IndexedKroneckerReader.degreeWord,pairFst_pair,pairSnd_pair,
    BinaryNat.succ_eq_bits,BinaryNatCode.encode,Nat.fromBitsLE_bits,Nat.sub_add_cancel hm]
  by_cases hk : k=1
  · subst k
    simp only [ite_true,Polynomial.coeff_X_one,Int.cast_one]
    simpa only [BinaryNatCode.encode] using ArithmeticBits.one_residueBits m
  · simp only [hk,ite_false,Polynomial.coeff_X,Int.cast_ite,Int.cast_one,Int.cast_zero]
    rw [ite_eq_right (Ne.symm hk)]
    simp [residueBits,BinaryNatCode.encode]

noncomputable def polynomial (word : List Bool → List Bool) (c : List Bool) : ℤ[X] :=
  (TermView.term (word c)).eval (fun _ => X)

def size (word : List Bool → List Bool) (c : List Bool) := (TermView.normalize (word c)).length

theorem size_unary (word : List Bool → List Bool) (hw : word∈FP) : UnaryFn (size word) :=
  UnaryFn.length (mem_FP_comp hw TermView.normalize_mem_FP)

theorem size_eq (word : List Bool → List Bool) (c : List Bool) :
    size word c=(TermView.term (word c)).toData.size := by
  rw [size,TermView.normalize_eq_term,Data.length_toBits]

noncomputable def coordinates (word : List Bool → List Bool) : Coordinates (Source.ofTerm word) where
  numerator _ _ := X
  denominator _ _ := 1
  numeratorCode := variableValue
  denominatorCode := IndexedKroneckerReader.unitValue
  numerator_eq c i _ k m hm := variable_packet c i k m hm
  denominator_eq c i _ k m hm := IndexedKroneckerReader.unit_packet c i k m hm

theorem coordinates_polynomial (word : List Bool → List Bool) (c : List Bool) :
    (coordinates word).family.polynomial c=polynomial word c := by
  rw [polynomial,(TermView.term (word c)).eval_eq_indexed_sum _ _ ((Source.ofTerm word).scope c)]
  simp only [Coordinates.family,Source.family,coordinates,Source.syntax,Source.ofTerm,
    RationalSubstitution.IntegerBits.Family.polynomial,RationalSubstitution.Indexed.cleared,
    one_pow,mul_one]
  have HC (z : ℤ) : (C z : ℤ[X])=(z : ℤ[X]) := by
    simpa only [Int.cast_id] using map_intCast (C : ℤ →+* ℤ[X]) z
  simp only [HC]

theorem coefficient_evaluator (word : List Bool → List Bool) (hw : word∈FP) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial word)) := by
  have E := (coordinates word).evaluator (Source.ofTerm_polyTime hw)
    (SpaceFunction.ofFP _ variableValue_FP) (SpaceFunction.ofFP _ IndexedKroneckerReader.unitValue_FP)
  refine E.congr (funext fun q => ?_)
  change PrimitivePairBits.coefficient (coordinates word).family.polynomial q= _
  simp only [PrimitivePairBits.coefficient,coordinates_polynomial]

theorem degree_bound (word : List Bool → List Bool) (c : List Bool) :
    (polynomial word c).natDegree≤size word c := by
  simpa only [polynomial,size_eq,Nat.mul_one] using
    (TermView.term (word c)).eval_natDegree_le_size (fun _ => (X : ℤ[X])) 1 (fun _ => by rw [natDegree_X])

theorem mass_bound (word : List Bool → List Bool) (c : List Bool) :
    coefficientMass (polynomial word c)≤2^size word c := by
  have HX : coefficientMass (X : ℤ[X])=1 := by
    simpa only [← Polynomial.C_mul_X_pow_eq_monomial,Polynomial.C_1,one_mul,pow_one,Int.natAbs_one] using
      coefficientMass_monomial 1 (1 : ℤ)
  have H := (TermView.term (word c)).eval_nestedMass_le_size (fun _ => C (X : ℤ[X])) 0
    (fun _ => by rw [NestedMass.C,HX]; decide)
  rw [← Term.eval_hom Polynomial.C (TermView.term (word c)) (fun _ => (X : ℤ[X])),NestedMass.C] at H
  simpa only [size_eq,polynomial,Nat.zero_add,Nat.mul_one] using H

noncomputable def source (word : List Bool → List Bool) : IntegerPolynomialRootQueriesBits.Source where
  polynomial := polynomial word
  degree := size word
  mass := size word
  degree_bound := degree_bound word
  mass_bound := mass_bound word

theorem access (word : List Bool → List Bool) (hw : word∈FP) : IntegerPolynomialRootQueriesBits.Access (source word) where
  coefficient := coefficient_evaluator word hw
  degree := BinaryFn.ofUnary (size_unary word hw)
  mass := BinaryFn.ofUnary (size_unary word hw)

theorem degree_evaluator (word : List Bool → List Bool) (hw : word∈FP) :
    SpaceFunction (fun c => BinaryNatCode.encode (polynomial word c).natDegree) :=
  IntegerPolynomialBits.degreeEvaluator (polynomial word) (coefficient_evaluator word hw)
    (size word) (size word) (BinaryFn.ofUnary (size_unary word hw)) (BinaryFn.ofUnary (size_unary word hw))
    (degree_bound word) (mass_bound word)

end LeanCanny.ETR.IntegerUnivariateTermSource

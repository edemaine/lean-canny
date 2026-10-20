/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeZeroFP
public import LeanCanny.ETR.FinitePolynomialCoefficientPadding
public import LeanCanny.ETR.CollectedCoefficientZero

/-! # Polynomial-space coefficient access to the zero-source tube

The FP syntax writer supplies the collected-coefficient evaluator. Native
coordinate queries have proved padding and renaming round trips. Every nonzero
coefficient is representable. Negativity and zero testing are in PSPACE.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeZero
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding
open Algebra.RationalSubstitution.Indexed Algebra.MatrixPower

def size (n : List Bool → ℕ) (active : List Bool → List Bool) (c : List Bool) : ℕ :=
  CollectedCoefficient.dimension (write n active) c

noncomputable def coefficient (n : List Bool → ℕ) (active target : List Bool → List Bool) (c : List Bool) : ℤ :=
  CollectedCoefficient.coefficient (write n active) target c

noncomputable def value (n : List Bool → ℕ) (active target modulus : List Bool → List Bool) : List Bool → List Bool :=
  CollectedCoefficient.value (write n active) target modulus

noncomputable def evaluator (n : List Bool → ℕ) (active target modulus : List Bool → List Bool)
    (hn : UnaryFn n) (ha : active ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value n active target modulus) :=
  CollectedCoefficient.evaluator (write n active) target modulus (write_mem_FP hn ha) ht hm

theorem source_term (n : List Bool → ℕ) (active : List Bool → List Bool) (c : List Bool) :
    TermView.term (write n active c) = term (n c) (active c) := by rw [write, TermView.term_toBits]

theorem dimension_le_size (n : List Bool → ℕ) (active : List Bool → List Bool) (c : List Bool) :
    dimension (n c) ≤ size n active c := by
  have h := CollectedCoefficient.arity_le_dimension (write n active) c
  rw [source_term, arity_term] at h
  exact h

noncomputable def paddedExponent (n : ℕ) (m : Coordinate n →₀ ℕ) (i : ℕ) : ℕ :=
  if hi : i < dimension n then m ((coordinateEquiv n).symm ⟨i, hi⟩) else 0

theorem exponentVector_padded (n : ℕ) (m : Coordinate n →₀ ℕ) :
    exponentVector (dimension n) (paddedExponent n m) = m.mapDomain (coordinateEquiv n) := by
  ext i
  simp only [exponentVector, Finsupp.coe_equivFunOnFinite_symm, paddedExponent, i.isLt, dite_true, Finsupp.mapDomain_equiv_apply]

noncomputable def exponentCode (n : List Bool → ℕ) (active : List Bool → List Bool) (c : List Bool)
    (m : Coordinate (n c) →₀ ℕ) : List Bool :=
  FixedWidthNatVector.encode (size n active c) (size n active c + 1) (paddedExponent (n c) m)

@[simp] theorem exponentCode_length (n : List Bool → ℕ) (active : List Bool → List Bool) (c : List Bool)
    (m : Coordinate (n c) →₀ ℕ) :
    (exponentCode n active c m).length = size n active c * (size n active c + 1) := FixedWidthNatVector.length_encode _ _ _

theorem coefficient_eq_native (n : List Bool → ℕ) (active target : List Bool → List Bool) (c : List Bool)
    (m : Coordinate (n c) →₀ ℕ) (ht : target c = exponentCode n active c m)
    (hm : ∀ j, m j < 2 ^ (size n active c + 1)) :
    coefficient n active target c = (TubePolynomial.integerPolynomial (0 : MvPolynomial (Fin (n c)) ℤ) (activeSet (n c) (active c))).coeff m := by
  have hfit : ∀ i < size n active c, paddedExponent (n c) m i < 2 ^ (size n active c + 1) := by
    intro i _
    unfold paddedExponent
    split_ifs
    · exact hm _
    · exact Nat.two_pow_pos _
  have h := CollectedCoefficient.coefficient_eq_of_encoded_target (write n active) target c (paddedExponent (n c) m) ht hfit
  rw [source_term] at h
  change coefficient n active target c = (Term.finitePolynomial (size n active c) (term (n c) (active c))).coeff
    (exponentVector (size n active c) (paddedExponent (n c) m)) at h
  rw [Term.coeff_finitePolynomial_padding (term (n c) (active c)) (dimension (n c)) (size n active c)
    (by rw [arity_term]) (dimension_le_size n active c) (paddedExponent (n c) m)
    (by intro i hi _; unfold paddedExponent; exact dite_eq_right (by omega)),
    finitePolynomial_term, exponentVector_padded,
      MvPolynomial.coeff_rename_mapDomain (coordinateEquiv (n c)) (coordinateEquiv (n c)).injective] at h
  exact h

theorem value_eq_native (n : List Bool → ℕ) (active target modulus : List Bool → List Bool) (c : List Bool)
    (m : Coordinate (n c) →₀ ℕ) (ht : target c = exponentCode n active c m)
    (hm : ∀ j, m j < 2 ^ (size n active c + 1)) :
    value n active target modulus c = residueBits
      (((TubePolynomial.integerPolynomial (0 : MvPolynomial (Fin (n c)) ℤ) (activeSet (n c) (active c))).coeff m : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)) :=
  congrArg (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (modulus c) + 1))) (coefficient_eq_native n active target c m ht hm)

theorem native_exponent_fits (n : List Bool → ℕ) (active : List Bool → List Bool) (c : List Bool)
    (m : Coordinate (n c) →₀ ℕ)
    (hm : (TubePolynomial.integerPolynomial (0 : MvPolynomial (Fin (n c)) ℤ) (activeSet (n c) (active c))).coeff m ≠ 0) :
    ∀ j, m j < 2 ^ (size n active c + 1) := by
  intro j
  have hi := MvPolynomial.monomial_le_degreeOf j (MvPolynomial.mem_support_iff.mpr hm)
  have hd := TubePolynomial.integer_polynomial_degree (0 : MvPolynomial (Fin (n c)) ℤ) (activeSet (n c) (active c))
  simp only [MvPolynomial.totalDegree_zero, max_eq_right (Nat.zero_le 2)] at hd
  have he := hi.trans ((MvPolynomial.degreeOf_le_totalDegree _ j).trans hd)
  have hsize := dimension_le_size n active c
  have hdim : 5 ≤ dimension (n c) := by unfold dimension constraintCount; omega
  exact he.trans_lt ((show 4 < size n active c + 1 by omega).trans (Nat.lt_two_pow_self))

noncomputable def negativeEvaluator (n : List Bool → ℕ) (active target : List Bool → List Bool)
    (hn : UnaryFn n) (ha : active ∈ FP) (ht : target ∈ FP) :
    SpaceFunction (fun c => if coefficient n active target c < 0 then [true] else []) :=
  CollectedCoefficient.negativeEvaluator (write n active) target (write_mem_FP hn ha) ht

theorem negativeLanguage_mem_PSPACE (n : List Bool → ℕ) (active target : List Bool → List Bool)
    (hn : UnaryFn n) (ha : active ∈ FP) (ht : target ∈ FP) : {c | coefficient n active target c < 0} ∈ PSPACE :=
  CollectedCoefficient.negativeLanguage_mem_PSPACE (write n active) target (write_mem_FP hn ha) ht

noncomputable def zeroDecider (n : List Bool → ℕ) (active target : List Bool → List Bool)
    (hn : UnaryFn n) (ha : active ∈ FP) (ht : target ∈ FP) : SpaceDecider {c | coefficient n active target c = 0} :=
  CollectedCoefficient.zeroDecider (write n active) target (write_mem_FP hn ha) ht

theorem zeroLanguage_mem_PSPACE (n : List Bool → ℕ) (active target : List Bool → List Bool)
    (hn : UnaryFn n) (ha : active ∈ FP) (ht : target ∈ FP) : {c | coefficient n active target c = 0} ∈ PSPACE :=
  (zeroDecider n active target hn ha ht).mem_PSPACE

end LeanCanny.ETR.TubeZero

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformSquarefreeExceptional
public import LeanCanny.Algebra.PolynomialPrincipalCoefficientSpace
public import LeanCanny.Algebra.BivariateDerivativeSpace
public import LeanCanny.Algebra.BivariateReaderCanonical
public import LeanCanny.Algebra.PrincipalParameterMass
public import LeanCanny.Algebra.ZeroAwarePolynomialSpace
public import LeanCanny.Algebra.PolynomialFamilyProductSpace

/-! # Native uniform squarefree exceptional polynomials

All principal orders are streamed from the original bivariate reader.
Identically zero principal factors are detected in polynomial space and
replaced by one; no GCD-order metadata routine is assumed.
-/

@[expose] public section
namespace LeanCanny.Algebra.UniformSquarefreeExceptionalBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower PrincipalSubresultant
open RationalSubstitution.IntegerBits (context selectedDegree)
open scoped Classical BigOperators

noncomputable def family (p : List Bool → (ℤ[X])[X]) (D : List Bool → ℕ) : PolynomialPrincipalCoefficientBits.Family where
  left := p
  right c := (p c).derivative
  leftDegree := D
  rightDegree c := D c - 1

noncomputable def access {p : List Bool → (ℤ[X])[X]} {D : List Bool → ℕ}
    (R : CertifiedPolynomial.BivariateReader p) (hD : BinaryFn D) :
    PolynomialPrincipalCoefficientBits.Access (family p D) where
  left := R
  right := CertifiedPolynomial.BivariateDerivative.reader R
  leftDegree := hD
  rightDegree := hD.sub (BinaryFn.const 1)

noncomputable def principal (p : List Bool → (ℤ[X])[X]) (D : List Bool → ℕ) : List Bool → ℤ[X] :=
  PolynomialPrincipalCoefficientBits.polynomial (family p D)

theorem principalEvaluator {p : List Bool → (ℤ[X])[X]} {D : List Bool → ℕ}
    (R : CertifiedPolynomial.BivariateReader p) (hD : BinaryFn D) :
    SpaceFunction (PrimitivePairBits.coefficient (principal p D)) := by
  refine (PolynomialPrincipalCoefficientBits.evaluator (access R hD)).congr (funext fun z => ?_)
  rw [PolynomialPrincipalCoefficientBits.residueValue_eq]
  rfl

def principalDegree (D E : List Bool → ℕ) (r : List Bool) : ℕ :=
  (2 * D (pairFst r) + 1) * E (pairFst r)

def principalMass (D b : List Bool → ℕ) (r : List Bool) : ℕ :=
  parameterMassBound (2 * D (pairFst r)) (b (pairFst r) + (D (pairFst r)).size)

theorem principalDegree_binary {D E : List Bool → ℕ} (hD : BinaryFn D) (hE : BinaryFn E) :
    BinaryFn (principalDegree D E) :=
  ((((BinaryFn.const 2).mul hD).add (BinaryFn.const 1)).mul hE).comp pairFst_mem_FP

theorem principalMass_binary {D b : List Bool → ℕ} (hD : BinaryFn D) (hb : BinaryFn b) :
    BinaryFn (principalMass D b) := by
  have hR := (BinaryFn.const 2).mul (hD.comp pairFst_mem_FP)
  have hb' : BinaryFn (fun r => b (pairFst r)) := hb.comp pairFst_mem_FP
  have hD' : BinaryFn (fun r => D (pairFst r)) := hD.comp pairFst_mem_FP
  have ha := hb'.add hD'.size
  exact ((hR.size.mul hR).add (hR.mul ha)).add ha

theorem principal_degree_le (p : List Bool → (ℤ[X])[X]) (D E : List Bool → ℕ)
    (hp : ∀ c k, ((p c).coeff k).natDegree ≤ E c) (r : List Bool) :
    (principal p D r).natDegree ≤ principalDegree D E r := by
  apply (signedPsc_parameter_degree (p (pairFst r)) (p (pairFst r)).derivative
    _ _ _ _ (hp _) (SymbolicScaledSquarefree.derivative_inner_degree _ _ (hp _))).trans
  exact Nat.mul_le_mul_right _ (by dsimp [family]; omega)

theorem principal_mass_le (p : List Bool → (ℤ[X])[X]) (D b : List Bool → ℕ)
    (hd : ∀ c, (p c).natDegree ≤ D c)
    (hp : ∀ c k, coefficientMass ((p c).coeff k) ≤ 2 ^ b c) (r : List Bool) :
    coefficientMass (principal p D r) ≤ 2 ^ principalMass D b r := by
  apply signedPsc_mass_le _ _ _ _ _ _ _ (by dsimp [family]; omega)
  · intro i
    exact (hp _ i).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  · intro i
    apply (SymbolicScaledSquarefree.derivative_coefficient_mass _ _ (hp _) i).trans
    exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (Nat.size_le_size (hd _)) _)

noncomputable def nonzeroPrincipal (p : List Bool → (ℤ[X])[X]) (D : List Bool → ℕ) : List Bool → ℤ[X] :=
  ZeroAwarePolynomialBits.polynomial (principal p D)

theorem nonzeroPrincipalEvaluator {p : List Bool → (ℤ[X])[X]} {D E b : List Bool → ℕ}
    (R : CertifiedPolynomial.BivariateReader p) (hD : BinaryFn D) (hE : BinaryFn E) (hb : BinaryFn b)
    (hd : ∀ c, (p c).natDegree ≤ D c)
    (he : ∀ c k, ((p c).coeff k).natDegree ≤ E c)
    (hm : ∀ c k, coefficientMass ((p c).coeff k) ≤ 2 ^ b c) :
    SpaceFunction (PrimitivePairBits.coefficient (nonzeroPrincipal p D)) :=
  ZeroAwarePolynomialBits.coefficientEvaluator _ (principalEvaluator R hD)
    _ _ (principalDegree_binary hD hE) (principalMass_binary hD hb)
    (principal_degree_le p D E he) (principal_mass_le p D b hd hm)

noncomputable def leading (p : List Bool → (ℤ[X])[X]) (D : List Bool → ℕ) (c : List Bool) : ℤ[X] :=
  (p c).coeff (D c)

def leadingQuery (D : List Bool → ℕ) (q : List Bool) : List Bool :=
  pair (pair (context q) (pairSnd q))
    (pair (BinaryNat.normalize (selectedDegree q)) (BinaryNatCode.encode (D (context q))))

theorem leadingQuery_FP {D : List Bool → ℕ} (hD : BinaryFn D) : leadingQuery D ∈ FP :=
  mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)
    (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.selectedDegree_mem_FP BinaryNat.normalize_mem_FP)
      (BinaryFn.bits_mem_FP (hD.comp RationalSubstitution.IntegerBits.context_mem_FP)))

theorem leadingEvaluator {p : List Bool → (ℤ[X])[X]} {D : List Bool → ℕ}
    (R : CertifiedPolynomial.BivariateReader p) (hD : BinaryFn D) :
    SpaceFunction (PrimitivePairBits.coefficient (leading p D)) := by
  refine (R.evaluator.precompose (leadingQuery D) (leadingQuery_FP hD)).congr (funext fun q => ?_)
  change R.coefficient (leadingQuery D q) = _
  rw [leadingQuery, BinaryNat.normalize_eq_bits]
  change R.coefficient (pair (pair (context q) (pairSnd q))
    (pair (BinaryNatCode.encode (Nat.fromBitsLE (selectedDegree q))) (BinaryNatCode.encode (D (context q))))) = _
  refine (R.coefficient_eq (pair (context q) (pairSnd q))
    (Nat.fromBitsLE (selectedDegree q)) (D (context q))).trans ?_
  change RationalSubstitution.IntegerBits.coefficientResidue _ _ =
    RationalSubstitution.IntegerBits.coefficientResidue _ _
  apply congrArg₂ RationalSubstitution.IntegerBits.coefficientResidue
  · simp only [pairFst_pair]
    rfl
  · simp only [pairSnd_pair]

def previous (r : List Bool) : List Bool :=
  pair (pairFst r) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd r) - 1))

theorem previous_FP : previous ∈ FP :=
  mem_FP_pair pairFst_mem_FP
    (BinaryFn.bits_mem_FP ((BinaryFn.fromBits pairSnd_mem_FP).sub (BinaryFn.const 1)))

noncomputable def factor (p : List Bool → (ℤ[X])[X]) (D : List Bool → ℕ) (r : List Bool) : ℤ[X] :=
  if Nat.fromBitsLE (pairSnd r) = 0 then leading p D (pairFst r)
  else nonzeroPrincipal p D (previous r)

theorem factorEvaluator {p : List Bool → (ℤ[X])[X]} {D E b : List Bool → ℕ}
    (R : CertifiedPolynomial.BivariateReader p) (hD : BinaryFn D) (hE : BinaryFn E) (hb : BinaryFn b)
    (hd : ∀ c, (p c).natDegree ≤ D c)
    (he : ∀ c k, ((p c).coeff k).natDegree ≤ E c)
    (hm : ∀ c k, coefficientMass ((p c).coeff k) ≤ 2 ^ b c) :
    SpaceFunction (PrimitivePairBits.coefficient (factor p D)) := by
  have L := PolynomialFamilyProductBits.reindexEvaluator (leadingEvaluator R hD) pairFst pairFst_mem_FP
  have P := PolynomialFamilyProductBits.reindexEvaluator (nonzeroPrincipalEvaluator R hD hE hb hd he hm) previous previous_FP
  have hi := BinaryFn.fromBits (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)
  have H := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (pairSnd (context q)) = 0))
    (hi.eq (BinaryFn.const 0)).flag_mem_FP L P
  refine H.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq, Function.comp_apply, PrimitivePairBits.coefficient, factor]
  split_ifs <;> rfl

noncomputable def polynomial (p : List Bool → (ℤ[X])[X]) (D : List Bool → ℕ) : List Bool → ℤ[X] :=
  PolynomialFamilyProductBits.polynomial (factor p D) (fun c => D c + 1)

theorem evaluator {p : List Bool → (ℤ[X])[X]} {D E b : List Bool → ℕ}
    (R : CertifiedPolynomial.BivariateReader p) (hD : BinaryFn D) (hE : BinaryFn E) (hb : BinaryFn b)
    (hd : ∀ c, (p c).natDegree ≤ D c)
    (he : ∀ c k, ((p c).coeff k).natDegree ≤ E c)
    (hm : ∀ c k, coefficientMass ((p c).coeff k) ≤ 2 ^ b c) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial p D)) :=
  PolynomialFamilyProductBits.evaluator _ _ (hD.add (BinaryFn.const 1))
    (factorEvaluator R hD hE hb hd he hm)

theorem polynomial_eq (p : List Bool → (ℤ[X])[X]) (D : List Bool → ℕ)
    (hd : ∀ c, (p c).natDegree = D c) (c : List Bool) :
    polynomial p D c = UniformSquarefreeExceptional.polynomial (p c) := by
  unfold polynomial PolynomialFamilyProductBits.polynomial
  rw [Finset.prod_range_succ']
  simp only [factor, previous, leading, nonzeroPrincipal, ZeroAwarePolynomialBits.polynomial,
    principal, PolynomialPrincipalCoefficientBits.polynomial, family,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false, ite_true]
  rw [← hd c]
  simp only [UniformSquarefreeExceptional.polynomial, UniformSquarefreeExceptional.factor,
    Polynomial.leadingCoeff, Polynomial.natDegree_derivative]
  exact mul_comm _ _

def degreeBound (D E : List Bool → ℕ) (c : List Bool) : ℕ :=
  E c + D c * ((2 * D c + 1) * E c)

def massBound (D b : List Bool → ℕ) (c : List Bool) : ℕ :=
  (D c + 1) * (b c + parameterMassBound (2 * D c) (b c + (D c).size))

theorem degreeBound_binary {D E : List Bool → ℕ} (hD : BinaryFn D) (hE : BinaryFn E) :
    BinaryFn (degreeBound D E) :=
  hE.add (hD.mul ((((BinaryFn.const 2).mul hD).add (BinaryFn.const 1)).mul hE))

theorem massBound_binary {D b : List Bool → ℕ} (hD : BinaryFn D) (hb : BinaryFn b) :
    BinaryFn (massBound D b) := by
  have hR := (BinaryFn.const 2).mul hD
  have ha := hb.add hD.size
  exact (hD.add (BinaryFn.const 1)).mul (hb.add (((hR.size.mul hR).add (hR.mul ha)).add ha))

theorem degree_le (p : List Bool → (ℤ[X])[X]) (D E : List Bool → ℕ)
    (hd : ∀ c, (p c).natDegree = D c) (he : ∀ c k, ((p c).coeff k).natDegree ≤ E c) (c : List Bool) :
    (polynomial p D c).natDegree ≤ degreeBound D E c := by
  rw [polynomial_eq p D hd]
  simpa only [degreeBound, hd] using UniformSquarefreeExceptional.degree_le (p c) (E c) (he c)

theorem mass_le (p : List Bool → (ℤ[X])[X]) (D b : List Bool → ℕ)
    (hd : ∀ c, (p c).natDegree ≤ D c)
    (hm : ∀ c k, coefficientMass ((p c).coeff k) ≤ 2 ^ b c) (c : List Bool) :
    coefficientMass (polynomial p D c) ≤ 2 ^ massBound D b c := by
  apply PolynomialFamilyProductBits.mass_le (factor p D) (fun c => D c + 1)
    (fun c => b c + parameterMassBound (2 * D c) (b c + (D c).size)) ?_ c
  intro z i
  simp only [factor, pairFst_pair, pairSnd_pair]
  split_ifs
  · exact (hm z _).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  · apply (ZeroAwarePolynomialBits.mass_le (principal p D) (principalMass D b)
      (principal_mass_le p D b hd hm) _).trans
    apply Nat.pow_le_pow_right (by decide)
    simp only [principalMass, previous, pairFst_pair]
    exact Nat.le_add_left _ _

theorem ne_zero (p : List Bool → (ℤ[X])[X]) (D : List Bool → ℕ)
    (hd : ∀ c, (p c).natDegree = D c) (hp : ∀ c, p c ≠ 0) (c : List Bool) :
    polynomial p D c ≠ 0 := by
  rw [polynomial_eq p D hd]
  exact UniformSquarefreeExceptional.ne_zero _ (hp c)

theorem avoids_exceptional {K : Type*} [Field K] (phi : ℤ[X] →+* K)
    (p : List Bool → (ℤ[X])[X]) (D : List Bool → ℕ)
    (hd : ∀ c, (p c).natDegree = D c) (c : List Bool)
    (ht : phi (polynomial p D c) ≠ 0) : phi (SymbolicScaledSquarefree.exceptional (p c)) ≠ 0 := by
  rw [polynomial_eq p D hd] at ht
  exact UniformSquarefreeExceptional.avoids_exceptional phi (p c) ht

end LeanCanny.Algebra.UniformSquarefreeExceptionalBits

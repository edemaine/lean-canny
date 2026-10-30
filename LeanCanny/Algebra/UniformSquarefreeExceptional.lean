/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicSquarefreeExceptional
public import LeanCanny.Algebra.SymbolicScaledSquarefreeBounds
public import LeanCanny.Algebra.PrincipalSubresultant.Signed
public import LeanCanny.Algebra.PrincipalParameterDegree

/-! # Uniform exceptional factors without a GCD-order metadata oracle

Multiply the leading coefficient by every nonzero signed principal
subresultant of the polynomial and its derivative. Identically zero factors
are replaced by one. The resulting nonzero polynomial excludes the selected
GCD-order principal factor, without requiring that order to be FP metadata.
-/

@[expose] public section
namespace LeanCanny.Algebra.UniformSquarefreeExceptional
open Polynomial PrincipalSubresultant SymbolicScaledSquarefree
open scoped Classical BigOperators

noncomputable def factor (p : Polynomial Coefficient) (j : ℕ) : Coefficient :=
  let a := signedPsc p p.derivative p.natDegree p.derivative.natDegree j
  if a = 0 then 1 else a

noncomputable def polynomial (p : Polynomial Coefficient) : Coefficient :=
  p.leadingCoeff * ∏ j ∈ Finset.range p.natDegree, factor p j

theorem factor_ne_zero (p : Polynomial Coefficient) (j : ℕ) : factor p j ≠ 0 := by
  dsimp only [factor]
  split_ifs with h
  · exact one_ne_zero
  · exact h

theorem ne_zero (p : Polynomial Coefficient) (hp : p ≠ 0) : polynomial p ≠ 0 :=
  mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp)
    (Finset.prod_ne_zero_iff.mpr (fun j _ => factor_ne_zero p j))

private lemma order_le (p : Polynomial Coefficient) : SymbolicScaledSquarefree.degree p ≤ p.natDegree - 1 := by
  by_cases hd : p.natDegree = 0
  · simp only [SymbolicScaledSquarefree.degree, hd, dite_true]
    omega
  · have hdeg : (fractionPolynomial p).natDegree = p.natDegree := natDegree_map_eq_of_injective embedding_injective p
    have hne : (fractionPolynomial p).derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
    have h := natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right (fractionPolynomial p) (fractionPolynomial p).derivative) hne
    rw [natDegree_derivative, hdeg] at h
    simpa only [degree_eq_common, SquarefreePart.common] using h

/-- Avoidance of the uniform product implies avoidance of the precise
squarefree exceptional factor used by the root covering construction. -/
theorem avoids_exceptional {K : Type*} [Field K] (phi : Coefficient →+* K)
    (p : Polynomial Coefficient) (ht : phi (polynomial p) ≠ 0) : phi (exceptional p) ≠ 0 := by
  have hs : phi p.leadingCoeff ≠ 0 ∧ ∀ j < p.natDegree, phi (factor p j) ≠ 0 := by
    simpa only [polynomial, map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff, Finset.mem_range] using ht
  by_cases hd : p.natDegree = 0
  · simpa only [exceptional, hd, ite_true, mul_one] using hs.1
  · have hk := order_le p
    have hkle : SymbolicScaledSquarefree.degree p ≤ min p.natDegree p.derivative.natDegree := by
      rw [natDegree_derivative]
      omega
    have hn : signedPsc p p.derivative p.natDegree p.derivative.natDegree (SymbolicScaledSquarefree.degree p) ≠ 0 := by
      rw [signedPsc_of_le _ _ hkle]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (degree_psc_ne_zero p hd)
    have h := hs.2 (SymbolicScaledSquarefree.degree p) (by omega)
    rw [factor, ite_eq_right hn, signedPsc_of_le _ _ hkle, map_mul] at h
    have hpsc := (mul_ne_zero_iff.mp h).2
    simpa only [exceptional, ite_eq_right hd, map_mul, mul_ne_zero_iff] using And.intro hs.1 hpsc

theorem degree_le (p : Polynomial Coefficient) (E : ℕ) (hp : ∀ k, (p.coeff k).natDegree ≤ E) :
    (polynomial p).natDegree ≤ E + p.natDegree * ((2 * p.natDegree + 1) * E) := by
  have hf (j : ℕ) : (factor p j).natDegree ≤ (2 * p.natDegree + 1) * E := by
    dsimp only [factor]
    split_ifs
    · simp
    · apply (signedPsc_parameter_degree p p.derivative _ _ j E hp (derivative_inner_degree p E hp)).trans
      apply Nat.mul_le_mul_right E
      have h := Polynomial.natDegree_derivative_le p
      omega
  apply Polynomial.natDegree_mul_le.trans
  apply Nat.add_le_add (hp p.natDegree)
  apply (Polynomial.natDegree_prod_le _ _).trans
  exact (Finset.sum_le_sum (fun j _ => hf j)).trans_eq (by simp)

end LeanCanny.Algebra.UniformSquarefreeExceptional

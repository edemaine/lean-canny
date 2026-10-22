/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MvCoefficientDerivation
public import LeanCanny.Algebra.CriticalValueAlgebraic

/-! # Multivariate chain rule with varying coefficients

Differentiate both the coefficients and the evaluation point. If the
coefficient derivation fixes a polynomial, only the usual gradient term
remains. This allows symbolic parameters to be held fixed while other
coefficient-field generators are differentiated.
-/

@[expose] public section

namespace LeanCanny.Algebra.MvCoefficientChainRule
open MvPolynomial
open scoped BigOperators

variable {K B L ι : Type*} [Field K] [Field B] [Field L]
  [Algebra K B] [Algebra K L] [Algebra B L]

theorem derivation_map_algebraMap (D : Derivation K B B) (p : MvPolynomial ι K) :
    MvCoefficientDerivation.derivation D (p.map (algebraMap K B)) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [map_C, MvCoefficientDerivation.derivation_C, D.map_algebraMap, C_0]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p i hp =>
    simp only [map_mul, map_X, Derivation.leibniz, smul_eq_mul, MvCoefficientDerivation.derivation_X,
      hp, mul_zero, add_zero]

variable [Fintype ι]

theorem chain_rule (D : Derivation K B B) (δ : Derivation K L L)
    (hD : ∀ b : B, δ (algebraMap B L b) = algebraMap B L (D b))
    (p : MvPolynomial ι B) (x : ι → L) :
    δ (aeval x p) = aeval x (MvCoefficientDerivation.derivation D p) +
      ∑ i, aeval x (pderiv i p) * δ (x i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [aeval_C, MvCoefficientDerivation.derivation_C, pderiv_C, map_zero, zero_mul,
      Finset.sum_const_zero, add_zero, hD]
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
    ring
  | mul_X p j hp =>
    have hd : MvCoefficientDerivation.derivation D (p * X j) = X j * MvCoefficientDerivation.derivation D p := by
      rw [Derivation.leibniz, MvCoefficientDerivation.derivation_X, smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
    rw [hd]
    simp only [map_mul, aeval_X, δ.leibniz, smul_eq_mul, hp,
      CriticalValueAlgebraic.eval_pderiv_mul_X, add_mul, Finset.sum_add_distrib]
    simp [mul_assoc, ← Finset.mul_sum, ite_mul, add_comm]
    ring

theorem chain_rule_of_fixed (D : Derivation K B B) (δ : Derivation K L L)
    (hD : ∀ b : B, δ (algebraMap B L b) = algebraMap B L (D b))
    (p : MvPolynomial ι B) (x : ι → L) (hp : MvCoefficientDerivation.derivation D p = 0) :
    δ (aeval x p) = ∑ i, aeval x (pderiv i p) * δ (x i) := by
  rw [chain_rule D δ hD, hp, map_zero, zero_add]

end LeanCanny.Algebra.MvCoefficientChainRule

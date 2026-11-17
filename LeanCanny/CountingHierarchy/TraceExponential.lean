/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CoefficientEvaluation
public import LeanCanny.CountingHierarchy.Factorial
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# The finite-field truncated exponential used in characteristic reconstruction

Uniform coefficient access evaluates a polynomial by one short-index sum.
One further sum evaluates its degree-`D` truncated exponential, using modular
factorials rather than constructing them. A final Fourier sum extracts the
indexed coefficient. All three stages have fixed counting depth even for
exponential `D`.

This module certifies the algebraic expression in Section 3 of the October 4,
2026 preprint. Identifying its coefficients with matrix characteristic
coefficients requires the separate trace/Newton identity; this module does not
assume or assert that missing identification.
-/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM Polynomial
open scoped BigOperators

/-- The polynomial specified by coefficient slots zero through `D`. -/
@[expose] noncomputable def coefficientPolynomial {K : Type*} [CommRing K]
    (D : ℕ) (c : ℕ → K) : Polynomial K :=
  ∑ k ∈ Finset.range (D + 1), Polynomial.C (c k) * Polynomial.X ^ k

/-- The polynomial expression whose low coefficients reconstruct the
characteristic polynomial when the input coefficients are negative traces divided by their indices. -/
@[expose] noncomputable def truncatedExponential {K : Type*} [Field K]
    (D : ℕ) (c : ℕ → K) : Polynomial K :=
  ∑ j ∈ Finset.range (D + 1), Polynomial.C ((j.factorial : K)⁻¹) *
    coefficientPolynomial D c ^ j

theorem coefficientPolynomial_degree {K : Type*} [CommRing K] (D : ℕ) (c : ℕ → K) :
    (coefficientPolynomial D c).natDegree ≤ D := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((Polynomial.natDegree_X_pow_le k).trans (by have := Finset.mem_range.mp hk; omega))

/-- The final Fourier extraction needs a prime larger than this quadratic degree bound. -/
theorem truncatedExponential_degree {K : Type*} [Field K] (D : ℕ) (c : ℕ → K) :
    (truncatedExponential D c).natDegree ≤ D * D := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  exact Polynomial.natDegree_pow_le.trans
    (Nat.mul_le_mul (by have := Finset.mem_range.mp hj; omega)
      (coefficientPolynomial_degree D c))

/-- Modular evaluation of a polynomial from its uniform coefficient residues. -/
@[expose] noncomputable def coefficientPolynomialResidue (p D z : ℕ) (c : ℕ → ℕ) : ℕ :=
  (∑ k ∈ Finset.range (D + 1), c k * powMod p z k) % p

/-- Modular evaluation of the truncated exponential, using only short indices. -/
@[expose] noncomputable def truncatedExponentialResidue (p D z : ℕ) (c : ℕ → ℕ) : ℕ :=
  (∑ j ∈ Finset.range (D + 1),
    powMod p (factorialResidue p j) (p - 2) *
      powMod p (coefficientPolynomialResidue p D z c) j) % p

/-- Coefficient reconstruction is one more uniform Fourier sum. -/
@[expose] noncomputable def truncatedExponentialCoefficient (p D k : ℕ) (c : ℕ → ℕ) : ℕ :=
  coefficientResidue p k (fun z => truncatedExponentialResidue p D z c)

theorem coefficientPolynomialResidue_cast {p : ℕ} [Fact p.Prime] (D z : ℕ) (c : ℕ → ℕ) :
    (coefficientPolynomialResidue p D z c : ZMod p) =
      (coefficientPolynomial D (fun k => (c k : ZMod p))).eval (z : ZMod p) := by
  simp only [coefficientPolynomialResidue, ZMod.natCast_mod, Nat.cast_sum,
    coefficientPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Nat.cast_mul,
    powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, ZMod.natCast_mod, Nat.cast_pow]

theorem truncatedExponentialResidue_cast {p : ℕ} [Fact p.Prime] {D : ℕ}
    (hD : D < p) (z : ℕ) (c : ℕ → ℕ) :
    (truncatedExponentialResidue p D z c : ZMod p) =
      (truncatedExponential D (fun k => (c k : ZMod p))).eval (z : ZMod p) := by
  simp only [truncatedExponentialResidue, ZMod.natCast_mod, Nat.cast_sum,
    truncatedExponential, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [factorialResidue_inverse (by have := Finset.mem_range.mp hj; omega),
    powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, ZMod.natCast_mod,
    Nat.cast_pow, coefficientPolynomialResidue_cast]

/-- Correct canonical coefficients of the actual truncated-exponential polynomial. -/
theorem truncatedExponentialCoefficient_eq {p : ℕ} [Fact p.Prime] {D k : ℕ}
    (hD : D < p) (hdegree : D * D < p - 1) (hk : k < p - 1) (c : ℕ → ℕ) :
    truncatedExponentialCoefficient p D k c =
      ((truncatedExponential D (fun i => (c i : ZMod p))).coeff k).val := by
  apply coefficientResidue_eq_val
    (truncatedExponential D (fun i => (c i : ZMod p))) k
    (fun z => truncatedExponentialResidue p D z c)
    ((truncatedExponential_degree D _).trans_lt hdegree) hk
  intro z _
  exact truncatedExponentialResidue_cast hD z c

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ}

/-- One sum evaluates a coefficient-specified polynomial with binary degree bound. -/
theorem coefficientPolynomialResidue_mem (E : Decoder enc) {p D z : α → ℕ}
    {c : α × ℕ → ℕ} (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat) (hz : ComputableInPolyTime z enc encNat)
    (hc : c ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => coefficientPolynomialResidue (p w) (D w) (z w) (fun k => c (w, k))) ∈
      CountingFunction (a + 1) enc encNat := by
  have hp' := hp.comp (ComputableInPolyTime.fst enc encNat)
  have hz' := hz.comp (ComputableInPolyTime.fst enc encNat)
  have hpower := CountingFunction.powMod (a := a) (CountingFunction.of_polyTime hp')
    (CountingFunction.of_polyTime hz')
    (CountingFunction.of_polyTime (ComputableInPolyTime.snd enc encNat))
  exact CountingFunction.nat_mod
    (CountingFunction.sum_range E (CountingFunction.nat_mul hc hpower)
      (ComputableInPolyTime.binary_add' hD (.const 1)))
    (CountingFunction.of_polyTime hp)

/-- The factorial and inner-sum oracles combine at one fixed maximum level. -/
theorem truncatedExponentialResidue_mem (E : Decoder enc) {p D z : α → ℕ}
    {c : α × ℕ → ℕ} (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat) (hz : ComputableInPolyTime z enc encNat)
    (hc : c ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => truncatedExponentialResidue (p w) (D w) (z w) (fun k => c (w, k))) ∈
      CountingFunction (max (a + 1) 3 + 1) enc encNat := by
  have hp' := hp.comp (ComputableInPolyTime.fst enc encNat)
  have hs := coefficientPolynomialResidue_mem E hp hD hz hc
  have hs' := CountingFunction.preprocess (input := encPair enc encNat) hs
    (g := fun q : α × ℕ => q.1) (ComputableInPolyTime.fst enc encNat)
  have hfac := CountingFunction.preprocess (input := encPair enc encNat) factorialResidue_mem
    (g := fun q : α × ℕ => (p q.1, q.2)) (hp'.prod (ComputableInPolyTime.snd _ _))
  have hinv := CountingFunction.powMod (a := max (a + 1) 3)
    (CountingFunction.of_polyTime hp') (CountingFunction.mono (Nat.le_max_right _ _) hfac)
    (CountingFunction.of_polyTime (ComputableInPolyTime.binary_sub' hp' (.const 2)))
  have hpower := CountingFunction.powMod (a := max (a + 1) 3)
    (CountingFunction.of_polyTime hp') (CountingFunction.mono (Nat.le_max_left _ _) hs')
    (CountingFunction.of_polyTime (ComputableInPolyTime.snd enc encNat))
  exact CountingFunction.nat_mod
    (CountingFunction.sum_range E (CountingFunction.nat_mul hinv hpower)
      (ComputableInPolyTime.binary_add' hD (.const 1)))
    (CountingFunction.of_polyTime hp)

/-- Indexed truncated-exponential coefficients are available at fixed depth.
This certificate constructs the sums and modular denominators rather than
assuming an exponential-sized matrix or coefficient oracle. -/
theorem truncatedExponentialCoefficient_mem (E : Decoder enc) {p D k : α → ℕ}
    {c : α × ℕ → ℕ} (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat) (hk : ComputableInPolyTime k enc encNat)
    (hc : c ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => truncatedExponentialCoefficient (p w) (D w) (k w) (fun i => c (w, i))) ∈
      CountingFunction (max (a + 1) 3 + 2) enc encNat := by
  have hc' := CountingFunction.preprocess
    (input := encPair (encPair enc encNat) encNat) hc
    (g := fun q : (α × ℕ) × ℕ => (q.1.1, q.2)) (by fun_prop)
  have heval := truncatedExponentialResidue_mem (Decoder.pair E Decoder.nat)
    (hp.comp (ComputableInPolyTime.fst enc encNat))
    (hD.comp (ComputableInPolyTime.fst enc encNat))
    (ComputableInPolyTime.snd enc encNat) hc'
  exact coefficientResidue_mem E hp hk heval

end LeanCanny.CountingHierarchy

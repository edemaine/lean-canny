/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FallingFactorial
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Range
public import Mathlib.Algebra.Polynomial.Derivative

/-! # Evaluating binary-order derivatives from implicit coefficients

The evaluator visits coefficients through one binary bounded sum. Derivative
orders and polynomial degrees need only short binary encodings.
-/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators

@[expose] noncomputable def derivativeResidue (p D k z : ℕ) (c : ℕ → ℕ) : ℕ :=
  (∑ j ∈ Finset.range (D + 1), if j + k ≤ D then
    c (j + k) * fallingFactorialResidue p (j + k) k * powMod p z j else 0) % p

/-- An `F_a` coefficient evaluator yields derivative values in
`F_(max(a,3)+1)`, uniformly in the binary derivative order. -/
theorem derivativeResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p D k z : α → ℕ} {c : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat)
    (hk : ComputableInPolyTime k enc encNat)
    (hz : ComputableInPolyTime z enc encNat)
    (hc : c ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => derivativeResidue (p w) (D w) (k w) (z w) (fun i => c (w, i))) ∈
      CountingFunction (max a 3 + 1) enc encNat := by
  have hp' := hp.comp (ComputableInPolyTime.fst enc encNat)
  have hD' := hD.comp (ComputableInPolyTime.fst enc encNat)
  have hk' := hk.comp (ComputableInPolyTime.fst enc encNat)
  have hz' := hz.comp (ComputableInPolyTime.fst enc encNat)
  have hj := ComputableInPolyTime.snd enc encNat
  have hjk := ComputableInPolyTime.binary_add' hj hk'
  have hcoeff := CountingFunction.preprocess hc
    ((ComputableInPolyTime.fst enc encNat).prod hjk)
  have hfall := fallingFactorialResidue_mem hp' hjk hk'
  have hpower := CountingFunction.powMod (a := max a 3)
    (CountingFunction.of_polyTime hp') (CountingFunction.of_polyTime hz')
    (CountingFunction.of_polyTime hj)
  have hvalue := CountingFunction.nat_mul
    (CountingFunction.nat_mul (CountingFunction.mono (Nat.le_max_left _ _) hcoeff)
      (CountingFunction.mono (Nat.le_max_right _ _) hfall)) hpower
  have htest : ComputableInPolyTime
      (fun q : α × ℕ => decide (q.2 + k q.1 ≤ D q.1)) (encPair enc encNat) encBool := by
    fun_prop
  have hterm := CountingFunction.ite (CountingFunction.of_polyTime htest) hvalue
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 0))
  have hsum := CountingFunction.sum_range E hterm
    (ComputableInPolyTime.binary_add' hD (.const 1))
  simpa only [derivativeResidue, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.nat_mod hsum (CountingFunction.of_polyTime hp)

/-- Correctness holds for every derivative order, including orders above the
polynomial degree, without expanding a derivative as an input polynomial. -/
theorem derivativeResidue_cast {p D k z : ℕ} [Fact p.Prime]
    (q : Polynomial (ZMod p)) (hq : q.natDegree ≤ D) (hD : D < p)
    (c : ℕ → ℕ) (hc : ∀ i ≤ D, (c i : ZMod p) = q.coeff i) :
    (derivativeResidue p D k z c : ZMod p) =
      (Polynomial.derivative^[k] q).eval (z : ZMod p) := by
  have hdegree : (Polynomial.derivative^[k] q).natDegree < D + 1 :=
    (Polynomial.natDegree_iterate_derivative q k).trans_lt (by omega)
  conv_rhs => rw [(Polynomial.derivative^[k] q).as_sum_range' (D + 1) hdegree]
  rw [derivativeResidue, ZMod.natCast_mod, Nat.cast_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Polynomial.eval_monomial, Polynomial.coeff_iterate_derivative, nsmul_eq_mul]
  by_cases hjk : j + k ≤ D
  · rw [ite_eq_left hjk, Nat.cast_mul, Nat.cast_mul, hc (j + k) hjk,
      fallingFactorialResidue_cast (hjk.trans_lt hD),
      powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, ZMod.natCast_mod, Nat.cast_pow]
    ring
  · rw [ite_eq_right hjk, Nat.cast_zero,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < j + k)]
    simp

end LeanCanny.CountingHierarchy

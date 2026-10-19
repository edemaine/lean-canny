/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.Sturm.Infinity
public import LeanCanny.Algebra.ScaledSignQueries
public import Mathlib.Data.Rat.Cast.Order

/-!
# Tarski queries from signed remainders and coefficient signs

The reference formula uses only field arithmetic, leading coefficients, and degrees.
For rational inputs it can be interpreted over ℚ throughout, while its answer is
the sign sum at distinct real roots. This is a mathematical correctness theorem;
it does not certify the workspace of Euclidean polynomial division.
-/

@[expose] public section

namespace LeanCanny.Algebra.Sturm
open Polynomial

variable {K L : Type*} [Field K] [Field L] [DecidableEq K] [DecidableEq L]

/-- Signed remainder sequences commute with injective field coefficient maps. -/
theorem map_sturmSeq (φ : K →+* L) (p q : K[X]) :
    (sturmSeq p q).map (Polynomial.map φ) = sturmSeq (p.map φ) (q.map φ) := by
  induction p, q using Polynomial.sturmSeq.induct with
  | case1 q => simp
  | case2 p q hp ih =>
    have hm : p.map φ ≠ 0 := Polynomial.map_ne_zero hp
    rw [sturmSeq_cons hp, List.map_cons, sturmSeq_cons hm, ih]
    rw [Polynomial.map_mod, Polynomial.map_neg]

variable [LinearOrder K] [LinearOrder L]

/-- The coefficient-only whole-line query formula. No roots are used in this definition. -/
noncomputable def coefficientQuery (p q : K[X]) : ℤ :=
  (signVariationsAtBot (sturmSeq p (q * p.derivative)) : ℤ) -
    signVariationsAtTop (sturmSeq p (q * p.derivative))

/-- Changing coefficients along a sign-preserving field map preserves the answer. -/
theorem coefficientQuery_map (φ : K →+* L)
    (hs : ∀ x, SignType.sign (φ x) = SignType.sign x) (p q : K[X]) :
    coefficientQuery (p.map φ) (q.map φ) = coefficientQuery p q := by
  have ht (cs : List K[X]) : signVariationsAtTop (cs.map (Polynomial.map φ)) =
      signVariationsAtTop cs := by
    rw [signVariationsAtTop_def, signVariationsAtTop_def]
    apply List.signVariations_congr
    simp only [List.map_map]
    apply List.map_congr_left
    intro p _
    change SignType.sign (p.map φ).leadingCoeff = SignType.sign p.leadingCoeff
    rw [leadingCoeff_map]
    exact hs _
  have hb (cs : List K[X]) : signVariationsAtBot (cs.map (Polynomial.map φ)) =
      signVariationsAtBot cs := by
    rw [signVariationsAtBot_def, signVariationsAtBot_def]
    apply List.signVariations_congr
    simp only [List.map_map]
    apply List.map_congr_left
    intro p _
    change SignType.sign ((p.map φ).leadingCoeff * (-1) ^ (p.map φ).natDegree) =
      SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree)
    rw [leadingCoeff_map, natDegree_map]
    simpa only [map_mul, map_pow, map_neg, map_one] using
      hs (p.leadingCoeff * (-1) ^ p.natDegree)
  simp only [coefficientQuery, Polynomial.derivative_map, ← Polynomial.map_mul,
    ← map_sturmSeq, ht, hb]

end LeanCanny.Algebra.Sturm

namespace LeanCanny.Algebra.RootSignQueries
open Polynomial Sturm
open scoped Classical

/-- Each semantic Tarski query equals a difference of coefficient sign variations. -/
theorem tarskiQuery_eq_coefficientQuery (p q : ℝ[X]) :
    tarskiQuery p q = coefficientQuery p q :=
  (sum_sign_sturmSeq_univ p q).symm

/-- Rational field arithmetic suffices for rational-input Tarski queries at real roots. -/
theorem tarskiQuery_rat (p q : ℚ[X]) :
    tarskiQuery (p.map (algebraMap ℚ ℝ)) (q.map (algebraMap ℚ ℝ)) = coefficientQuery p q := by
  rw [tarskiQuery_eq_coefficientQuery]
  apply coefficientQuery_map
  intro x
  change SignType.sign (x : ℝ) = SignType.sign x
  simp only [sign_apply, Rat.cast_pos, Rat.cast_lt_zero]

/-- Integer input coefficients can be promoted to ℚ for the same query formula. -/
theorem tarskiQuery_int (p q : ℤ[X]) :
    tarskiQuery (p.map (algebraMap ℤ ℝ)) (q.map (algebraMap ℤ ℝ)) =
      coefficientQuery (p.map (algebraMap ℤ ℚ)) (q.map (algebraMap ℤ ℚ)) := by
  simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℤ ℚ ℝ] using
    tarskiQuery_rat (p.map (algebraMap ℤ ℚ)) (q.map (algebraMap ℤ ℚ))

/-- Substituting the coefficient formula removes every semantic root query from
the scaled sign-pattern count. The exponential query family remains explicit. -/
theorem scaledRootCount_eq_sturm {J : Type*} [Fintype J] (p : ℝ[X])
    (Q : J → ℝ[X]) (σ : J → SignType) :
    scaledRootCount p Q σ =
      ∑ e : J → Fin 3, patternWeight σ e * coefficientQuery p (queryPolynomial Q e) := by
  simp only [scaledRootCount, tarskiQuery_eq_coefficientQuery]

end LeanCanny.Algebra.RootSignQueries

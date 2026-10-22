/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Adapted for lean-canny from TauCeti at revision 034e577c895d28c058d92af4036f7ce0b03081cf.
Source: Algebra/Polynomial/OfFn.lean.
Changes: selected algebraic proof slice, project namespace, and pinned Mathlib
compatibility. See STURM_SOURCES.md.
-/
module

public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! # Algebraic principal subresultant identities

Adapted proof slice for the signed determinant formula used in Sturm–Tarski queries.
See STURM_SOURCES.md for the upstream source and omitted material.
-/

public section

namespace LeanCanny.Algebra.PrincipalSubresultant

open Polynomial List

section

open Polynomial

variable {R : Type*} [Semiring R] [DecidableEq R]

omit [DecidableEq R] in
/-- Evaluating the coefficient vector reads the corresponding polynomial coefficient. -/
@[simp]
theorem toFn_apply (n : ℕ) (p : R[X]) (i : Fin n) :
    toFn n p i = p.coeff i := (rfl)

-- Mathlib's `ofFn` takes `[DecidableEq R]`, so this instance occurs in the statement.
/-- The coordinate vector with value one at `l` reconstructs the monomial `X ^ l.val`. -/
@[simp]
theorem ofFn_single {n : ℕ} (l : Fin n) :
    ofFn n (fun i => if i = l then (1 : R) else 0) = X ^ l.val := by
  simp [ofFn_eq_sum_monomial, apply_ite (monomial _), monomial_one_right_eq_X_pow]

/-- A polynomial of degree below `n` is recovered from its vector of first `n` coefficients.
This is the `degree` form of `Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt`, which also covers
the zero polynomial. -/
theorem ofFn_comp_toFn_eq_id_of_degree_lt {n : ℕ} {p : R[X]} (h : p.degree < n) :
    ofFn n (toFn n p) = p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · exact ofFn_comp_toFn_eq_id_of_natDegree_lt ((natDegree_lt_iff_degree_lt hp).mpr h)

end

end LeanCanny.Algebra.PrincipalSubresultant

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Adapted for lean-canny from TauCeti at revision 034e577c895d28c058d92af4036f7ce0b03081cf.
Source: Algebra/Polynomial/Coeff/Basic.lean.
Changes: selected algebraic proof slice, project namespace, and pinned Mathlib
compatibility. See STURM_SOURCES.md.
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
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

/-- The coefficients of `X ^ l * p` vanish outside the window from `l` to `l + n`
when `p.natDegree ≤ n`. -/
theorem coeff_X_pow_mul_of_natDegree_le {R : Type*} [Semiring R]
    {p : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) (l d : ℕ) :
    (X ^ l * p).coeff d = if l ≤ d ∧ d ≤ l + n then p.coeff (d - l) else 0 := by
  rw [coeff_X_pow_mul']
  by_cases h : l ≤ d
  · by_cases h' : d ≤ l + n
    · simp [h, h']
    · have hz : p.coeff (d - l) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [h, h', hz]
  · simp [h]

end

end LeanCanny.Algebra.PrincipalSubresultant

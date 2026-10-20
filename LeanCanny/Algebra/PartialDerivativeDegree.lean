/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Degrees
import Lean.Elab.Tactic.Omega

/-! # Degree bounds for formal partial derivatives

A nonzero coefficient in a partial derivative comes from a monomial one degree
higher in the original polynomial. The bound also covers zero polynomials and
positive characteristic, where additional coefficients can vanish.
-/

@[expose] public section

namespace LeanCanny.Algebra.PartialDerivativeDegree
open MvPolynomial

variable {ι R : Type*} [CommSemiring R]

theorem degree_le (p : MvPolynomial ι R) (i : ι) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  rw [totalDegree]
  apply Finset.sup_le
  intro m hm
  have hc : p.coeff (m + Finsupp.single i 1) ≠ 0 := by
    intro h
    have hn := MvPolynomial.mem_support_iff.mp hm
    rw [coeff_pderiv, h, zero_mul] at hn
    exact hn rfl
  have hd := le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  have he : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index]
    · simp
    · intro _ _
      rfl
    · intro _ _ _ _
      rfl
  rw [he] at hd
  omega

end LeanCanny.Algebra.PartialDerivativeDegree

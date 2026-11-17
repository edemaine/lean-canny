/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MvCoefficientMass

/-! # Exact natural-scalar scaling of multivariate integer coefficient mass -/

public section

namespace LeanCanny.Algebra.MvMass

open MvPolynomial
open scoped BigOperators

variable {ι : Type*}

theorem mass_nsmul (k : ℕ) (p : MvPolynomial ι ℤ) : mass (k • p) = k * mass p := by
  classical
  rw [mass_eq_sum (k • p) p.support MvPolynomial.support_smul, mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [nsmul_eq_mul, ← MvPolynomial.C_eq_natCast, MvPolynomial.coeff_C_mul,
    Int.natAbs_mul, Int.natAbs_natCast]

end LeanCanny.Algebra.MvMass

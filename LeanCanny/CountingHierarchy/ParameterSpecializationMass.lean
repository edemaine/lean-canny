/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ParameterMass
public import LeanCanny.CountingHierarchy.ParameterDegree
public import LeanCanny.CountingHierarchy.BivariateSpecializationMass

/-! # Multivariate coefficient mass after an integer parameter specialization -/

public section

namespace LeanCanny.CountingHierarchy

open LeanCanny.Algebra
open scoped BigOperators Classical

/-- Specialization can discard terms; summing over the original support
retains the bound without requiring an injective evaluation homomorphism. -/
theorem parameterSpecialization_mass_le {ι : Type*}
    (P : MvPolynomial ι (Polynomial ℤ)) (H : ℕ) (hH : HasParameterDegree P H)
    (R : ℤ) (hR : 1 ≤ R.natAbs) :
    MvMass.mass (P.map (Polynomial.evalRingHom R)) ≤
      ParameterMass.mass P * R.natAbs ^ H := by
  rw [MvMass.mass_eq_sum _ P.support (MvPolynomial.support_map_subset _ _)]
  simp only [MvPolynomial.coeff_map, Polynomial.coe_evalRingHom]
  calc
    _ ≤ ∑ e ∈ P.support, coefficientMass (P.coeff e) * R.natAbs ^ H :=
      Finset.sum_le_sum (fun e _ => natAbs_eval_le_mass (P.coeff e) H (hH e) R hR)
    _ = _ := by rw [← Finset.sum_mul, ParameterMass.mass]

/-- Only the binary exponent of the possibly enormous parameter is used
in the resulting logarithmic coefficient-mass budget. -/
theorem parameterSpecialization_mass_le_pow {ι : Type*}
    (P : MvPolynomial ι (Polynomial ℤ)) (H b s : ℕ) (hH : HasParameterDegree P H)
    (hb : ParameterMass.mass P ≤ 2 ^ b) :
    MvMass.mass (P.map (Polynomial.evalRingHom ((2 : ℤ) ^ s))) ≤ 2 ^ (b + s * H) := by
  have hR : 1 ≤ ((2 : ℤ) ^ s).natAbs := by
    simpa only [Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl] using (Nat.one_le_two_pow (n := s))
  apply (parameterSpecialization_mass_le P H hH _ hR).trans
  simpa only [Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl, ← pow_mul, ← pow_add] using
    Nat.mul_le_mul_right (((2 : ℤ) ^ s).natAbs ^ H) hb

end LeanCanny.CountingHierarchy

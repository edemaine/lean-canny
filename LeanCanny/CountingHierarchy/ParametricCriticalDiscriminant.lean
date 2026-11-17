/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ParametricCriticalSpecialization
public import LeanCanny.CountingHierarchy.DiscriminantSpecialization
public import LeanCanny.Algebra.IntegerRootBound

/-! # A nonzero integer discriminant for the critical-value deformation -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial

variable {n : ℕ}

/-- The derivative resultant of the actual critical-value polynomial. -/
@[expose] noncomputable def criticalDiscriminant (d : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) : Polynomial ℤ :=
  (parametricCriticalValue d F hF).resultant (parametricCriticalValue d F hF).derivative

/-- The explicit separated centers make this polynomial nonzero. -/
theorem criticalDiscriminant_ne_zero (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) :
    criticalDiscriminant d F hF ≠ 0 :=
  resultant_derivative_ne_zero_of_separable_map (parameterEvaluation (0 : ℂ)) _
    (parametricCriticalValue_monic d F hF)
    (parametricCriticalValue_at_zero_separable d hd F hF)

/-- An explicit coefficient-mass bound suffices to avoid all exceptional real
 parameters. Quantitative CH applications subsequently bound this mass. -/
theorem criticalValue_separable_of_large_parameter (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (u : ℝ)
    (hu : (LeanCanny.Algebra.coefficientMass (criticalDiscriminant d F hF) : ℝ) + 1 ≤ |u|) :
    ((parametricCriticalValue d F hF).map (parameterEvaluation u)).Separable := by
  apply separable_map_of_resultant_derivative_ne_zero (parameterEvaluation u) _
    (parametricCriticalValue_monic d F hF)
  intro hz
  have hb := LeanCanny.Algebra.abs_root_lt_coefficientMass_add_one
    (criticalDiscriminant d F hF) (criticalDiscriminant_ne_zero d hd F hF) u hz
  exact (not_lt_of_ge hu) hb

end LeanCanny.CountingHierarchy

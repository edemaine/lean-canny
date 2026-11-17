/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.BivariateSwapBounds
public import LeanCanny.Algebra.NestedCoefficientMass

/-! # Coefficient mass after selecting either bivariate coordinate -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped BigOperators

theorem bivariate_swap_coefficient_mass_le (P : Polynomial (Polynomial ℤ)) (i : ℕ) :
    coefficientMass ((Bivariate.swap P).coeff i) ≤ NestedMass.mass P := by
  rw [show coefficientMass ((Bivariate.swap P).coeff i) =
      ∑ j ∈ Finset.range (P.natDegree + 1), (((Bivariate.swap P).coeff i).coeff j).natAbs from
    (((Bivariate.swap P).coeff i).sum_over_range' (fun _ => rfl) _
      ((bivariate_swap_coefficient_degree_le P i).trans_lt (Nat.lt_succ_self _))),
    NestedMass.range_sum P (P.natDegree + 1) (Nat.lt_succ_self _)]
  apply Finset.sum_le_sum
  intro j _
  rw [bivariate_swap_coeff]
  exact coeff_natAbs_le_coefficientMass _ _

end LeanCanny.CountingHierarchy

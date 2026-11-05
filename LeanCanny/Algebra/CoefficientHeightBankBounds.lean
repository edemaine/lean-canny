/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientHeightBank
public import LeanCanny.Algebra.CoefficientMass

/-! # Preevaluation bounds for polynomial bank denominators

These bounds concern coefficients before parameter evaluation. They do not
bound evaluated denominators independently of the parameter.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoefficientHeightBank
open Polynomial
open scoped Classical BigOperators
variable {A : Type*} [CommRing A] {m : ℕ}

theorem commonDenominator_mass (x : CoefficientHeightBank ℤ[X] A m) (M : ℕ)
    (h : ∀ i, coefficientMass (x.denominator i) ≤ M) :
    coefficientMass x.commonDenominator ≤ M ^ m := by
  classical
  apply (coefficientMass_prod_le Finset.univ x.denominator).trans
  calc
    (∏ i : Fin m, coefficientMass (x.denominator i)) ≤ ∏ _i : Fin m, M :=
      Finset.prod_le_prod (fun i _ => h i)
    _ = M ^ m := by simp

theorem commonDenominator_degree (x : CoefficientHeightBank ℤ[X] A m) (D : ℕ)
    (h : ∀ i, (x.denominator i).natDegree ≤ D) :
    x.commonDenominator.natDegree ≤ m * D := by
  classical
  apply (Polynomial.natDegree_prod_le Finset.univ x.denominator).trans
  calc
    (∑ i : Fin m, (x.denominator i).natDegree) ≤ ∑ _i : Fin m, D :=
      Finset.sum_le_sum (fun i _ => h i)
    _ = m * D := by simp

theorem cofactor_mass (x : CoefficientHeightBank ℤ[X] A m) (i : Fin m) (M : ℕ)
    (h : ∀ j, coefficientMass (x.denominator j) ≤ M) :
    coefficientMass (x.cofactor i) ≤ M ^ (m - 1) := by
  classical
  apply (coefficientMass_prod_le (Finset.univ.erase i) x.denominator).trans
  calc
    (∏ j ∈ Finset.univ.erase i, coefficientMass (x.denominator j)) ≤
        ∏ _j ∈ Finset.univ.erase i, M :=
      Finset.prod_le_prod (fun j _ => h j)
    _ = M ^ (m - 1) := by simp

theorem cofactor_degree (x : CoefficientHeightBank ℤ[X] A m) (i : Fin m) (D : ℕ)
    (h : ∀ j, (x.denominator j).natDegree ≤ D) :
    (x.cofactor i).natDegree ≤ (m - 1) * D := by
  classical
  apply (Polynomial.natDegree_prod_le (Finset.univ.erase i) x.denominator).trans
  calc
    (∑ j ∈ Finset.univ.erase i, (x.denominator j).natDegree) ≤
        ∑ _j ∈ Finset.univ.erase i, D :=
      Finset.sum_le_sum (fun j _ => h j)
    _ = (m - 1) * D := by simp

end LeanCanny.Algebra.CoefficientHeightBank

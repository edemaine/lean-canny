/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableFiniteSigns
public import LeanCanny.Algebra.SymbolicFixedTableCoordinateBounds
public import LeanCanny.Algebra.BivariateRationalSubstitutionBounds

/-! # Bounds for cleared queries on the actual prepared rational coordinates -/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicFixedTableFinite.Family
open Polynomial SymbolicScaledSquarefree
open scoped Classical

theorem signQueryWith_degree (F : Family) (D : ℕ) (q : MvPolynomial (Fin F.count) Coefficient)
    (hD : ∀ i, q.degreeOf i ≤ D) :
    (F.signQueryWith (fun _ => D) q).natDegree ≤ 2 * F.count * D * F.exponent := by
  simpa only [signQueryWith, Fintype.card_fin] using BivariateRationalSubstitution.outer_degree_clearedWith q D F.exponent
    (fun i => (F.fixedCoordinate i).numerator) (fun i => (F.fixedCoordinate i).denominator) hD
    (fun i => (le_max_left _ _).trans (F.fixedCoordinate_bounds i).degree)
    (fun i => (le_max_right _ _).trans (F.fixedCoordinate_bounds i).degree)

theorem signQueryWith_inner_degree (F : Family) (D Ep : ℕ) (q : MvPolynomial (Fin F.count) Coefficient)
    (hD : ∀ i, q.degreeOf i ≤ D) (hp : ∀ e, (q.coeff e).natDegree ≤ Ep) (k : ℕ) :
    ((F.signQueryWith (fun _ => D) q).coeff k).natDegree ≤ Ep + 2 * F.count * D * F.exponent := by
  simpa only [signQueryWith, Fintype.card_fin] using BivariateRationalSubstitution.inner_degree_clearedWith q D Ep F.exponent
    (fun i => (F.fixedCoordinate i).numerator) (fun i => (F.fixedCoordinate i).denominator) hD hp
    (fun i => (F.fixedCoordinate_bounds i).numeratorInner) (fun i => (F.fixedCoordinate_bounds i).denominatorInner) k

theorem signQueryWith_mass (F : Family) (D s : ℕ) (q : MvPolynomial (Fin F.count) Coefficient)
    (hD : ∀ i, q.degreeOf i ≤ D) (hp : BivariateRationalSubstitution.sourceMass q ≤ 2 ^ s) :
    NestedMass.mass (F.signQueryWith (fun _ => D) q) ≤ 2 ^ (s + 2 * F.count * D * F.exponent) := by
  simpa only [signQueryWith, Fintype.card_fin] using BivariateRationalSubstitution.mass_clearedWith_uniform q D s F.exponent
    (fun i => (F.fixedCoordinate i).numerator) (fun i => (F.fixedCoordinate i).denominator) hD hp
    (fun i => (F.fixedCoordinate_bounds i).numeratorMass) (fun i => (F.fixedCoordinate_bounds i).denominatorMass)

theorem coordinate_numerator_encoded (F : Family) (B : ℕ) (hB : F.exponent < B) (i : Fin F.count) (k : ℕ) :
    (PolynomialKronecker.encode B (F.fixedCoordinate i).numerator).coeff k =
      ((F.fixedCoordinate i).numerator.coeff (k / B)).coeff (k % B) :=
  PolynomialKronecker.coefficient_any B (by omega) _
    (fun j => ((F.fixedCoordinate_bounds i).numeratorInner j).trans_lt hB) k

theorem coordinate_denominator_encoded (F : Family) (B : ℕ) (hB : F.exponent < B) (i : Fin F.count) (k : ℕ) :
    (PolynomialKronecker.encode B (F.fixedCoordinate i).denominator).coeff k =
      ((F.fixedCoordinate i).denominator.coeff (k / B)).coeff (k % B) :=
  PolynomialKronecker.coefficient_any B (by omega) _
    (fun j => ((F.fixedCoordinate_bounds i).denominatorInner j).trans_lt hB) k

end LeanCanny.Algebra.SymbolicFixedTableFinite.Family

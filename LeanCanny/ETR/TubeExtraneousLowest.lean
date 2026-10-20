/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeExtraneousBudget
public import LeanCanny.Algebra.DeformationLowestCoefficient

/-! # The lowest coefficient of the nonzero extraneous deformation

Coefficient-ring specialization remains nonzero because deformation at one is
one. Vanishing of the symbolic lowest coefficient is therefore equivalent
to an increase of the deformation order after specialization.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeExtraneous
open Complexity LeanCanny.Encoding LeanCanny.Algebra

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

theorem determinant_degree (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    (determinant source active n d ell c).natDegree ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) :=
  Macaulay.extraneous_deformation_degree (TubeBivariate.rows source active n d ell c) _ _

noncomputable def lowestCoefficient (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : Polynomial (Polynomial ℤ) :=
  (determinant source active n d ell c).trailingCoeff

theorem lowestCoefficient_ne_zero (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    lowestCoefficient source active n d ell c ≠ 0 :=
  Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (determinant_ne_zero source active n d ell c)

theorem determinant_map_ne_zero {K : Type*} [CommRing K] [Nontrivial K]
    (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (c : List Bool) (φ : Polynomial (Polynomial ℤ) →+* K) :
    (determinant source active n d ell c).map φ ≠ 0 := by
  have h : ((determinant source active n d ell c).map φ).eval 1 = 1 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_one, determinant_eval_one, map_one]
  intro hz
  rw [hz, Polynomial.eval_zero] at h
  exact zero_ne_one h

theorem lowestCoefficient_eval_zero_iff_order_increases {K : Type*} [CommRing K] [Nontrivial K]
    (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (c : List Bool) (φ : Polynomial (Polynomial ℤ) →+* K) :
    φ (lowestCoefficient source active n d ell c) = 0 ↔
      (determinant source active n d ell c).natTrailingDegree <
        ((determinant source active n d ell c).map φ).natTrailingDegree := by
  rw [lowestCoefficient, DeformationLowestCoefficient.map_trailingCoeff_eq_zero_iff,
    or_iff_right (determinant_map_ne_zero source active n d ell c φ)]

theorem lowestCoefficient_inner_degree (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) (j : ℕ) :
    ((lowestCoefficient source active n d ell c).coeff j).natDegree ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) *
        Nat.fromBitsLE (TubeCleared.uniformDegree source B.degree c) :=
  determinant_inner_degree source active n d ell B c _ j

end LeanCanny.ETR.TubeExtraneous

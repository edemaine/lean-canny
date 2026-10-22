/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeMacaulayKernelBasis
public import LeanCanny.Algebra.MacaulayRelationExtraneous

/-! # The extraneous factor in the tube relation determinant

The characteristic determinant of the actual tube's complementary relation
matrix factors by the extraneous characteristic determinant. This is a
comparison of relation determinants, not the resultant quotient formula for
the Macaulay numerator.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeMacaulayRelationFactor
open LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

noncomputable def higherFactor : Polynomial (Polynomial (Polynomial ℤ)) :=
  Macaulay.higherRelationFactor
    (Macaulay.subtractiveSystem (TubeBivariate.rows source active n d ell c)
      (MacaulayBits.Degrees (TubeCleared.layout source) c))
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (TubeMacaulayKernelBasis.width_bound source c)

theorem higherFactor_ne_zero : higherFactor source active n d ell c ≠ 0 :=
  Macaulay.higherRelationFactor_subtractive_ne_zero _ _ _ (TubeMacaulayKernelBasis.width_bound source c)

theorem characteristic_factorization :
    (AffineCharacteristic.subtractiveMatrix
      (Macaulay.relationMinor (TubeBivariate.rows source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
        (TubeMacaulayKernelBasis.width_bound source c))).det =
      (AffineCharacteristic.subtractiveMatrix
        (Macaulay.extraneousMinor (TubeBivariate.rows source active n d ell c)
          (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c)))).det *
        higherFactor source active n d ell c :=
  Macaulay.relation_characteristic_eq_extraneous_mul _ _ _ (TubeMacaulayKernelBasis.width_bound source c)

theorem extraneous_characteristic_dvd_relation_characteristic :
    (AffineCharacteristic.subtractiveMatrix
      (Macaulay.extraneousMinor (TubeBivariate.rows source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c)))).det ∣
      (AffineCharacteristic.subtractiveMatrix
        (Macaulay.relationMinor (TubeBivariate.rows source active n d ell c)
          (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
          (TubeMacaulayKernelBasis.width_bound source c))).det :=
  ⟨higherFactor source active n d ell c, characteristic_factorization source active n d ell c⟩

end LeanCanny.ETR.TubeMacaulayRelationFactor

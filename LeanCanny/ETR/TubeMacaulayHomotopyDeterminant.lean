/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeMacaulayGenericKoszul
public import LeanCanny.ETR.TubeMacaulayRelationFactor
public import LeanCanny.Algebra.MacaulayHomotopyDeterminant
public import LeanCanny.Algebra.KoszulHomotopyOperator

/-! # Concrete factors of the tube's finite homotopy determinant

The finite degree-one homotopy operator has the existing active, extraneous,
and higher-relation determinant factors. The characteristic identity holds
over the original polynomial coefficient ring. This does not establish
cancellation in the Macaulay numerator/extraneous quotient.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeMacaulayHomotopyDeterminant
open LeanCanny.Algebra
open scoped Classical Matrix

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

noncomputable def operator (k : ℕ) :
    Module.End TubeMacaulayWeightedKoszul.Coefficient (TubeMacaulayWeightedKoszul.piece source c (k + 1)) :=
  KoszulWeighted.homotopyOperator (TubeMacaulayGenericShift.system source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (TubeMacaulayWeightedKoszul.homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c) k

theorem operator_mem_range (k : ℕ) (x : TubeMacaulayWeightedKoszul.piece source c (k + 1))
    (hx : x ∈ LinearMap.range (TubeMacaulayPowerKoszul.homotopy source c k)) :
    operator source active n d ell c k x ∈ LinearMap.range (TubeMacaulayPowerKoszul.homotopy source c k) :=
  KoszulWeighted.homotopyOperator_mem_range _ _ _ (TubeMacaulayWeightedKoszul.homogeneous source active n d ell c)
    (TubeMacaulayKernelBasis.width_bound source c) k x hx

theorem generic_factorization :
    (TubeMacaulayGenericKoszul.contractionMatrix source active n d ell c 0).det =
      (Macaulay.activeMinor (TubeMacaulayGenericShift.system source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))).det *
      (Macaulay.extraneousMinor (TubeMacaulayGenericShift.system source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))).det *
      Macaulay.higherRelationFactor (TubeMacaulayGenericShift.system source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
        (TubeMacaulayKernelBasis.width_bound source c) :=
  KoszulWeighted.contractionMatrix_zero_full_factor _ _ _ (TubeMacaulayWeightedKoszul.homogeneous source active n d ell c)
    (TubeMacaulayKernelBasis.width_bound source c)

theorem characteristic_factorization :
    (AffineCharacteristic.subtractiveMatrix
      (KoszulWeighted.contractionMatrix (TubeBivariate.rows source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
        (TubeBivariate.rows_homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c) 0)).det =
      (AffineCharacteristic.subtractiveMatrix
        (Macaulay.activeMinor (TubeBivariate.rows source active n d ell c)
          (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c)))).det *
      (AffineCharacteristic.subtractiveMatrix
        (Macaulay.extraneousMinor (TubeBivariate.rows source active n d ell c)
          (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c)))).det *
        TubeMacaulayRelationFactor.higherFactor source active n d ell c :=
  KoszulWeighted.contractionMatrix_zero_characteristic_factor _ _ _ (TubeBivariate.rows_homogeneous source active n d ell c)
    (TubeMacaulayKernelBasis.width_bound source c)

end LeanCanny.ETR.TubeMacaulayHomotopyDeterminant

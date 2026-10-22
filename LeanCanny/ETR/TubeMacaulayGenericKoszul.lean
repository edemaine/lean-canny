/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeMacaulayPowerKoszul
public import LeanCanny.Algebra.KoszulGenericZero

/-! # Exactness of the actual finite generic shifted tube complex

The generic characteristic shift makes the finite weighted homotopy
operators invertible. The tube's homogeneous degrees and exponent-width
bound therefore give higher exactness of its actual weighted differential
maps and canonical matrices, with no additional algebraic certificates.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeMacaulayGenericKoszul
open LeanCanny.Algebra TubeMacaulayWeightedKoszul
open scoped Classical Matrix

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

noncomputable def differential (k : ℕ) : piece source c (k + 1) →ₗ[Coefficient] piece source c k :=
  KoszulWeighted.differential (TubeMacaulayGenericShift.system source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c)) (TubeCleared.matrixWidth (source c))
    (homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c) k

theorem exact (k : ℕ) :
    LinearMap.ker (differential source active n d ell c k) =
      LinearMap.range (differential source active n d ell c (k + 1)) :=
  KoszulWeighted.genericShift_weighted_exact (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (TubeBivariate.rows_homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c) k

theorem zero_surjective : Function.Surjective (differential source active n d ell c 0) :=
  KoszulWeighted.genericShift_weighted_zero_surjective (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (TubeBivariate.rows_homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c)

theorem matrix_kernel_iff (k : ℕ) (v : TubeMacaulayCanonicalKoszul.Index source c (k + 1) → Coefficient) :
    Matrix.vecMul v (TubeMacaulayCanonicalKoszul.matrix source active n d ell c k) = 0 ↔
      ∃ w : TubeMacaulayCanonicalKoszul.Index source c (k + 2) → Coefficient,
        Matrix.vecMul w (TubeMacaulayCanonicalKoszul.matrix source active n d ell c (k + 1)) = v :=
  KoszulWeighted.genericShift_matrix_kernel_iff (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (TubeBivariate.rows_homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c) k v

noncomputable def contractionMatrix (k : ℕ) :
    Matrix (TubeMacaulayCanonicalKoszul.Index source c (k + 1))
      (TubeMacaulayCanonicalKoszul.Index source c (k + 1)) Coefficient :=
  KoszulWeighted.contractionMatrix (TubeMacaulayGenericShift.system source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c) k

theorem contractionMatrix_det_ne_zero (k : ℕ) : (contractionMatrix source active n d ell c k).det ≠ 0 :=
  KoszulWeighted.contractionMatrix_genericShift_det_ne_zero (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (TubeBivariate.rows_homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c) k

end LeanCanny.ETR.TubeMacaulayGenericKoszul

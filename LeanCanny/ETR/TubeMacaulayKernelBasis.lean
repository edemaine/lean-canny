/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeMacaulayGenericShift
public import LeanCanny.Algebra.MacaulayRelationMinor

/-! # A Koszul basis of the generic shifted tube kernel

Removing the zero selected rows gives linearly independent relations and
unique kernel coordinates, specialized to the actual bivariate tube rows.
The basis and its inverse are algebraic constructions without space bounds.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeMacaulayKernelBasis
open LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

theorem width_bound : Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c) <
    2 ^ TubeCleared.matrixWidth (source c) := by
  have hW := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hW
  exact hW

noncomputable def basis :
    Module.Basis (Macaulay.RelationIndex (MacaulayBits.Degrees (TubeCleared.layout source) c)
        (TubeCleared.matrixWidth (source c))) (RatFunc (Polynomial (Polynomial ℤ)))
      (LinearMap.ker (Macaulay.fullMatrix (TubeMacaulayGenericShift.system source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))).vecMulLinear) :=
  Macaulay.genericShift_kernelBasis (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (width_bound source c) (TubeBivariate.rows_homogeneous source active n d ell c)

theorem kernel_iff_existsUnique
    (v : Macaulay.MultiplierIndex (MacaulayBits.Degrees (TubeCleared.layout source) c)
      (TubeCleared.matrixWidth (source c)) → RatFunc (Polynomial (Polynomial ℤ))) :
    Matrix.vecMul v (Macaulay.fullMatrix (TubeMacaulayGenericShift.system source active n d ell c)
      (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))) = 0 ↔
      ∃! w : Macaulay.RelationIndex (MacaulayBits.Degrees (TubeCleared.layout source) c)
          (TubeCleared.matrixWidth (source c)) → RatFunc (Polynomial (Polynomial ℤ)),
        Matrix.vecMul w (Macaulay.independentRelations (TubeMacaulayGenericShift.system source active n d ell c)
          (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
          (width_bound source c)) = v :=
  Macaulay.genericShift_kernel_iff_existsUnique _ _ _ (width_bound source c)
    (TubeBivariate.rows_homogeneous source active n d ell c) v

end LeanCanny.ETR.TubeMacaulayKernelBasis

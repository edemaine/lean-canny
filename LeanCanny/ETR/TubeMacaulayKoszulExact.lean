/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeMacaulayGenericShift
public import LeanCanny.Algebra.MacaulayKoszulContraction

/-! # Koszul relations span the generic shifted tube kernel

At the Macaulay level, the full multiplication matrix of the actual tube
system is exact at its multiplier space: its kernel is spanned by the
degree-compatible Koszul relations. The division relations supply a finite
generating family. This asserts neither higher exactness nor a resultant
quotient identity.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeMacaulayKoszulExact
open LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

theorem kernel_eq_koszulSpan :
    LinearMap.ker (Macaulay.fullMatrix (TubeMacaulayGenericShift.system source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))).vecMulLinear =
      Macaulay.koszulSpan (TubeMacaulayGenericShift.system source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c)) := by
  have hW := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hW
  exact Macaulay.genericShift_kernel_eq_koszulSpan _ _ _ hW
    (TubeBivariate.rows_homogeneous source active n d ell c)

theorem kernel_iff
    (v : Macaulay.MultiplierIndex (MacaulayBits.Degrees (TubeCleared.layout source) c)
      (TubeCleared.matrixWidth (source c)) → RatFunc (Polynomial (Polynomial ℤ))) :
    Matrix.vecMul v (Macaulay.fullMatrix (TubeMacaulayGenericShift.system source active n d ell c)
      (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))) = 0 ↔
      ∃ w : Macaulay.MultiplierIndex (MacaulayBits.Degrees (TubeCleared.layout source) c)
          (TubeCleared.matrixWidth (source c)) → RatFunc (Polynomial (Polynomial ℤ)),
        Matrix.vecMul w (Macaulay.divisionRelations (TubeMacaulayGenericShift.system source active n d ell c)
          (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
          (by
            have hW := TubeCleared.level_lt source c
            rw [MacaulayBits.level_eq] at hW
            exact hW)) = v := by
  have hW := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hW
  exact Macaulay.genericShift_kernel_iff _ _ _ hW
    (TubeBivariate.rows_homogeneous source active n d ell c) v

end LeanCanny.ETR.TubeMacaulayKoszulExact

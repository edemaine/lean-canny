/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeMacaulayKernelBasis
public import LeanCanny.Algebra.MacaulayLocalizedKoszul

/-! # All-degree Koszul exactness on the generic tube coordinate charts

Inverting any spatial coordinate makes the actual shifted tube inputs a
unit ideal. The resulting Koszul chain complex is exact in every positive
exterior degree, with a surjective degree-zero map and an explicit exterior
contracting homotopy. This is not yet the finite weighted-grade theorem.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeMacaulayLocalizedKoszul
open LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

abbrev ChartRing (source : List Bool → List Bool) (c : List Bool) (i : Fin (TubeParameter.spatialCount (source c))) :=
  Macaulay.CoordinateRing (TubeParameter.spatialCount (source c)) (Polynomial (Polynomial ℤ)) i

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

noncomputable def system (i : Fin (TubeParameter.spatialCount (source c))) :
    Fin (TubeParameter.spatialCount (source c)) → ChartRing source c i :=
  Macaulay.localizedSystem (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) i

theorem graded_exact (i : Fin (TubeParameter.spatialCount (source c))) (k : ℕ) :
    LinearMap.ker (KoszulExterior.gradedDifferential (system source active n d ell c i) k) =
      LinearMap.range (KoszulExterior.gradedDifferential (system source active n d ell c i) (k + 1)) :=
  Macaulay.localized_graded_exact _ _ (TubeCleared.matrixWidth (source c))
    (TubeBivariate.rows_homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c) i k

theorem complex_exact (i : Fin (TubeParameter.spatialCount (source c))) (k : ℕ) :
    LinearMap.ker ((KoszulExterior.complex (system source active n d ell c i)).d (k + 1) k).hom =
      LinearMap.range ((KoszulExterior.complex (system source active n d ell c i)).d (k + 2) (k + 1)).hom :=
  Macaulay.localized_complex_exact _ _ (TubeCleared.matrixWidth (source c))
    (TubeBivariate.rows_homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c) i k

theorem degree_zero_surjective (i : Fin (TubeParameter.spatialCount (source c))) :
    Function.Surjective (KoszulExterior.gradedDifferential (system source active n d ell c i) 0) :=
  Macaulay.localized_graded_zero_surjective _ _ (TubeCleared.matrixWidth (source c))
    (TubeBivariate.rows_homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c) i

theorem contracting_homotopy (i : Fin (TubeParameter.spatialCount (source c))) :
    ∃ v : Fin (TubeParameter.spatialCount (source c)) → ChartRing source c i,
      ∀ x : KoszulExterior.Total (ChartRing source c i) (Fin (TubeParameter.spatialCount (source c))),
        KoszulExterior.differential (system source active n d ell c i) (KoszulExterior.wedge v x) +
          KoszulExterior.wedge v (KoszulExterior.differential (system source active n d ell c i) x) = x :=
  Macaulay.localized_homotopy _ _ (TubeCleared.matrixWidth (source c))
    (TubeBivariate.rows_homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c) i

end LeanCanny.ETR.TubeMacaulayLocalizedKoszul

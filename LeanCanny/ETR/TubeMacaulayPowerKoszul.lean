/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeMacaulayCanonicalKoszul
public import LeanCanny.Algebra.KoszulWeightedContractionMatrix

/-! # Pure-power contraction on the tube's finite weighted pieces

The coordinate-power system with the tube's degrees has a polynomial
contracting homotopy on the same finite weighted pieces as the shifted tube.
This proves exactness of that pure-power complex. The transfer to the actual
generic shifted tube is proved in `TubeMacaulayGenericKoszul`.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeMacaulayPowerKoszul
open LeanCanny.Algebra TubeMacaulayWeightedKoszul
open scoped Classical Matrix

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

noncomputable def differential (source : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    piece source c (k + 1) →ₗ[Coefficient] piece source c k :=
  KoszulWeighted.differential (Macaulay.powers (MacaulayBits.Degrees (TubeCleared.layout source) c))
    (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c)) (TubeCleared.matrixWidth (source c))
    (KoszulWeighted.powers_homogeneous _) (TubeMacaulayKernelBasis.width_bound source c) k

noncomputable def homotopy (source : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    piece source c k →ₗ[Coefficient] piece source c (k + 1) :=
  KoszulWeighted.weightedHomotopy (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (TubeCleared.matrixWidth (source c)) (TubeMacaulayKernelBasis.width_bound source c) k

theorem homotopy_identity (source : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    (differential source c (k + 1)).comp (homotopy source c (k + 1)) +
      (homotopy source c k).comp (differential source c k) = LinearMap.id :=
  KoszulWeighted.weightedHomotopy_identity _ _ (TubeMacaulayKernelBasis.width_bound source c) k

theorem homotopy_zero_identity (source : List Bool → List Bool) (c : List Bool) :
    (differential source c 0).comp (homotopy source c 0) = LinearMap.id :=
  KoszulWeighted.weightedHomotopy_zero_identity _ _ (TubeMacaulayKernelBasis.width_bound source c)

theorem exact (source : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    LinearMap.ker (differential source c k) = LinearMap.range (differential source c (k + 1)) :=
  KoszulWeighted.powers_weighted_exact _ _ (TubeMacaulayKernelBasis.width_bound source c) k

theorem zero_surjective (source : List Bool → List Bool) (c : List Bool) :
    Function.Surjective (differential source c 0) :=
  KoszulWeighted.powers_weighted_zero_surjective _ _ (TubeMacaulayKernelBasis.width_bound source c)

noncomputable def homotopyMatrix (source : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    Matrix (TubeMacaulayCanonicalKoszul.Index source c k)
      (TubeMacaulayCanonicalKoszul.Index source c (k + 1)) Coefficient :=
  KoszulWeighted.homotopyMatrix (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (TubeCleared.matrixWidth (source c)) (TubeMacaulayKernelBasis.width_bound source c) k

end LeanCanny.ETR.TubeMacaulayPowerKoszul

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeMacaulayWeightedKoszul
public import LeanCanny.Algebra.MacaulayCanonicalMatrix

/-! # Canonical weighted Koszul matrices for the shifted tube

The finite tube pieces have monomial–subset bases. These give canonical
row-vector matrices with zero consecutive products. The first matrix,
reindexed by the proved Macaulay index equivalences, is the actual full
Macaulay multiplication matrix. Higher exactness is supplied in
`TubeMacaulayGenericKoszul`; resource-bounded entry readers remain open.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeMacaulayCanonicalKoszul
open LeanCanny.Algebra TubeMacaulayWeightedKoszul
open scoped Classical Matrix

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

abbrev Index (source : List Bool → List Bool) (c : List Bool) (k : ℕ) :=
  KoszulWeighted.CanonicalIndex (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c)) (TubeCleared.matrixWidth (source c)) k

noncomputable def basis (source : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    Module.Basis (Index source c k) Coefficient (piece source c k) :=
  KoszulWeighted.canonicalBasis _ _ _ _

instance piece_free (source : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    Module.Free Coefficient (piece source c k) := Module.Free.of_basis (basis source c k)

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

noncomputable def matrix (k : ℕ) : Matrix (Index source c (k + 1)) (Index source c k) Coefficient :=
  KoszulWeighted.canonicalMatrix (TubeMacaulayGenericShift.system source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c)) (TubeCleared.matrixWidth (source c))
    (homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c) k

theorem matrix_mul (k : ℕ) :
    matrix source active n d ell c (k + 1) * matrix source active n d ell c k = 0 :=
  KoszulWeighted.canonicalMatrix_mul _ _ _ _ (homogeneous source active n d ell c)
    (TubeMacaulayKernelBasis.width_bound source c) k

theorem matrix_zero_reindex :
    (matrix source active n d ell c 0).submatrix
      (KoszulWeighted.macaulaySourceEquiv (MacaulayBits.Degrees (TubeCleared.layout source) c)
        (TubeCleared.matrixWidth (source c)))
      (KoszulWeighted.macaulayTargetEquiv (MacaulayBits.Degrees (TubeCleared.layout source) c)
        (TubeCleared.matrixWidth (source c))) =
      Macaulay.fullMatrix (TubeMacaulayGenericShift.system source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c)) :=
  KoszulWeighted.canonicalMatrix_macaulay _ _ _ (homogeneous source active n d ell c)
    (TubeMacaulayKernelBasis.width_bound source c)

end LeanCanny.ETR.TubeMacaulayCanonicalKoszul

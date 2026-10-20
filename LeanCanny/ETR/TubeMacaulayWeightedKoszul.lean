/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeMacaulayKernelBasis
public import LeanCanny.Algebra.KoszulWeightedMatrix
public import LeanCanny.Algebra.MacaulayWeightedBridge

/-! # The finite weighted Koszul complex for the generic shifted tube

Every term is a finite coefficient-field vector space. The complex is zero
above the spatial arity, and its row-vector matrices have zero consecutive
products. This constructs the finite complex; higher exactness and entry
reader bounds for its chosen bases remain separate obligations.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeMacaulayWeightedKoszul
open LeanCanny.Algebra
open scoped Classical Matrix

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

abbrev Coefficient := RatFunc (Polynomial (Polynomial ℤ))

noncomputable def piece (source : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    Submodule Coefficient (KoszulWeighted.Total (TubeParameter.spatialCount (source c)) Coefficient) :=
  KoszulWeighted.space (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c)) (TubeCleared.matrixWidth (source c)) k

instance piece_finite (source : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    Module.Finite Coefficient (piece source c k) := KoszulWeighted.space_finite (R := Coefficient) _ _ _ _

theorem piece_eq_bot_of_lt (source : List Bool → List Bool) (c : List Bool) (k : ℕ)
    (hk : TubeParameter.spatialCount (source c) < k) : piece source c k = ⊥ :=
  KoszulWeighted.space_eq_bot_of_lt _ _ _ _ hk

theorem rank_bound (source : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    Module.finrank Coefficient (piece source c k) ≤ TubeParameter.spatialCount (source c) ^ k *
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) :=
  KoszulWeighted.finrank_space_le _ _ _ _

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

theorem homogeneous (i : Fin (TubeParameter.spatialCount (source c))) :
    (TubeMacaulayGenericShift.system source active n d ell c i).IsHomogeneous
      (MacaulayBits.Degrees (TubeCleared.layout source) c i) :=
  Macaulay.genericShift_homogeneous _ _ (TubeBivariate.rows_homogeneous source active n d ell c) i

noncomputable def complex : ChainComplex (ModuleCat Coefficient) ℕ :=
  KoszulWeighted.complex (TubeMacaulayGenericShift.system source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c)) (TubeCleared.matrixWidth (source c))
    (homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c)

noncomputable def matrix (k : ℕ) :
    Matrix (Fin (Module.finrank Coefficient (piece source c (k + 1))))
      (Fin (Module.finrank Coefficient (piece source c k))) Coefficient :=
  KoszulWeighted.matrix (TubeMacaulayGenericShift.system source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c)) (TubeCleared.matrixWidth (source c))
    (homogeneous source active n d ell c) (TubeMacaulayKernelBasis.width_bound source c) k

theorem matrix_mul (k : ℕ) :
    matrix source active n d ell c (k + 1) * matrix source active n d ell c k = 0 :=
  KoszulWeighted.matrix_mul _ _ _ _ (homogeneous source active n d ell c)
    (TubeMacaulayKernelBasis.width_bound source c) k

end LeanCanny.ETR.TubeMacaulayWeightedKoszul

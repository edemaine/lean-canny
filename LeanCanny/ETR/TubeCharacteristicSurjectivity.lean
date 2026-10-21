/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCharacteristicRoots
public import LeanCanny.Algebra.MacaulayQuotientSurjectivity

/-! # Surjectivity certificates for the concrete tube polynomial

Surjectivity of the specialized full Macaulay row map makes the constant
coefficient of the actual tube characteristic quotient a unit. Over a
nontrivial coefficient ring it is nonzero. The extraneous determinant may
vanish; no condition on its specialized value is imposed.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open LeanCanny.Algebra
open scoped Classical Matrix

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

private theorem surjectivity_width_bound (source : List Bool → List Bool) (c : List Bool) :
    Macaulay.level (MacaulayBits.Degrees (TubeCleared.layout source) c) < 2 ^ TubeCleared.matrixWidth (source c) := by
  have hw := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hw
  exact hw

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)
  {S : Type*} [CommRing S]

theorem polynomial_constant_map_isUnit_of_fullMatrix_surjective (φ : Polynomial (Polynomial ℤ) →+* S)
    (hsurj : Function.Surjective (fun v => Matrix.vecMul v (Macaulay.fullMatrix
      (fun i => (TubeBivariate.rows source active n d ell c i).map φ)
      (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))))) :
    IsUnit (φ ((polynomial source active n d ell c).coeff 0)) := by
  have hW := surjectivity_width_bound source c
  have hd : ∀ i : Fin (TubeParameter.spatialCount (source c)),
      0 < MacaulayBits.Degrees (TubeCleared.layout source) c i := fun i => TubeCleared.degree_pos source c i.val
  have hdegree := MacaulayUniversal.degree_lt_width _ _ hd hW
  have hp := fun i => (TubeBivariate.rows_homogeneous source active n d ell c i).map φ
  have he := MacaulayUniversal.polynomialValue_isUnit_of_fullMatrix_surjective
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c)) hdegree hW
    (fun i => (TubeBivariate.rows source active n d ell c i).map φ) hp hd hsurj
  have hv := MacaulayUniversal.polynomialValue_eq_eval_zero _ _ hdegree hW
    (fun i => (TubeBivariate.rows source active n d ell c i).map φ) hp hd
  have hm := Macaulay.characteristicQuotient_map φ (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
  have hz : Polynomial.eval (0 : S) (Macaulay.characteristicQuotient
      (fun i => (TubeBivariate.rows source active n d ell c i).map φ)
      (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))) =
      φ ((polynomial source active n d ell c).coeff 0) := by
    calc
      _ = Polynomial.eval (0 : S) ((polynomial source active n d ell c).map φ) :=
        (congrArg (Polynomial.eval (0 : S)) hm).symm
      _ = _ := by rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
  exact (hv.trans hz) ▸ he

theorem polynomial_constant_map_ne_zero_of_fullMatrix_surjective [Nontrivial S] (φ : Polynomial (Polynomial ℤ) →+* S)
    (hsurj : Function.Surjective (fun v => Matrix.vecMul v (Macaulay.fullMatrix
      (fun i => (TubeBivariate.rows source active n d ell c i).map φ)
      (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))))) :
    φ ((polynomial source active n d ell c).coeff 0) ≠ 0 :=
  (polynomial_constant_map_isUnit_of_fullMatrix_surjective source active n d ell c φ hsurj).ne_zero

end LeanCanny.ETR.TubeCharacteristicQuotient

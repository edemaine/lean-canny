/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationCoefficientMap
public import LeanCanny.Algebra.MacaulayExtraneousControl

/-! # The actual full tube extraneous minor and its nonzero deformation

The selected set contains exactly the unreduced monomials at the Macaulay
level. The identity-padded matrix represents the true extraneous principal
determinant. Perturbation, projection, and deformation remain independent;
the shared parameter radix preserves every selected coefficient.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeExtraneous
open LeanCanny.Encoding LeanCanny.Algebra

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree

noncomputable def indices (source : List Bool → List Bool) (c : List Bool) :
    Finset (Macaulay.Index (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c))) :=
  Macaulay.extraneousIndices (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))

noncomputable def matrix (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) :=
  Macaulay.extraneousPadded (TubeDeformation.system source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))

noncomputable def determinant (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) : Polynomial (Polynomial (Polynomial ℤ)) :=
  (matrix source active n d ell c).det

theorem determinant_eval_one (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) : (determinant source active n d ell c).eval 1 = 1 :=
  Macaulay.extraneous_deformation_eval_one (TubeBivariate.rows source active n d ell c) _ _

theorem determinant_ne_zero (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) : determinant source active n d ell c ≠ 0 :=
  Macaulay.extraneous_deformation_ne_zero (TubeBivariate.rows source active n d ell c) _ _

theorem determinant_inner_degree (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) (j k : ℕ) :
    (((determinant source active n d ell c).coeff j).coeff k).natDegree ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) *
        Nat.fromBitsLE (TubeCleared.uniformDegree source B.degree c) :=
  Macaulay.extraneous_deformation_inner_degree (TubeBivariate.rows source active n d ell c) _ _ _
    (TubeBivariate.rows_inner_bound source active n d ell B c) j k

noncomputable def encodedMatrix (source active degree : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) :=
  Macaulay.extraneousPadded
    (Macaulay.deformation (TubeDeformation.encodedRows source active degree n d ell c) (MacaulayBits.Degrees (TubeCleared.layout source) c))
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))

noncomputable def encodedDeterminant (source active degree : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) : Polynomial (Polynomial ℤ) := (encodedMatrix source active degree n d ell c).det

theorem encodedDeterminant_eq_map (source active degree : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) : encodedDeterminant source active degree n d ell c =
      (determinant source active n d ell c).map (PolynomialKronecker.encode (TubeDeformation.radix source degree c)) :=
  (Macaulay.det_extraneous_deformation_map (PolynomialKronecker.encode (TubeDeformation.radix source degree c))
    (TubeBivariate.rows source active n d ell c) (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))).symm

theorem coefficient_recovery (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) (i j k : ℕ)
    (hi : i < TubeDeformation.radix source B.degree c) :
    ((encodedDeterminant source active B.degree n d ell c).coeff j).coeff (i + TubeDeformation.radix source B.degree c * k) =
      (((determinant source active n d ell c).coeff j).coeff k).coeff i := by
  rw [encodedDeterminant_eq_map, Polynomial.coeff_map]
  exact PolynomialKronecker.coefficient _ _ (fun k => (determinant_inner_degree source active n d ell B c j k).trans_lt
    (Nat.lt_succ_self _)) i k hi

noncomputable def coefficient (source active inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : ℤ :=
  (((determinant source active n d ell c).coeff (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (middle c))).coeff (Nat.fromBitsLE (inner c))

theorem coefficient_zero_of_not_lt (source active inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool)
    (hi : ¬Nat.fromBitsLE (inner c) < TubeDeformation.radix source B.degree c) : coefficient source active inner middle outer n d ell c = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have hd := determinant_inner_degree source active n d ell B c (Nat.fromBitsLE (outer c)) (Nat.fromBitsLE (middle c))
  unfold TubeDeformation.radix at hi
  omega

end LeanCanny.ETR.TubeExtraneous

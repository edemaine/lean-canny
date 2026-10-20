/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationModular

/-! # Modular affine coefficients recover the original three parameters

The affine matrix is the coefficient reduction of the encoded integer tube
deformation. Below the first radix, coefficient recovery gives the original
perturbation/projection/deformation coefficient. Above it the coefficient is
zero by the proved full determinant degree allowance.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open Algebra.MatrixPower Algebra.RationalSubstitution
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det residueBits

noncomputable def encodedMatrix (source active degree : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) :=
  Macaulay.matrix (Macaulay.deformation (encodedRows source active degree n d ell c) (MacaulayBits.Degrees (TubeCleared.layout source) c))
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))

private theorem deformation_reduction {R S : Type*} [CommRing R] [CommRing S] {N : ℕ}
    (φ : R →+* S) (p : Fin N → MvPolynomial (Fin N) (Polynomial R)) (d : Fin N → ℕ) (W : ℕ) :
    (Macaulay.matrix (Macaulay.deformation p d) d W).map (Polynomial.mapRingHom (Polynomial.mapRingHom φ)) =
      fun r s => PolynomialAffineDeformation.affine (((Macaulay.matrix p d W).map (Polynomial.mapRingHom φ)) r s)
        (if r = s then 1 else 0) := by
  funext r s
  rw [Matrix.map_apply, Macaulay.matrix_deformation_entry]
  by_cases hrs : r = s
  all_goals
    simp only [PolynomialAffineDeformation.affine, Polynomial.coe_mapRingHom, Matrix.map_apply,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X,
      Matrix.one_apply, hrs, ite_true, ite_false,
      Polynomial.map_zero, Polynomial.map_one, map_zero, map_one]

theorem affine_matrix_reduction (source active modulus inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) :
    (modularFamily source active modulus inner middle outer n d ell B).matrix c =
      (encodedMatrix source active B.degree n d ell c).map (TubeBivariate.reduction (Nat.fromBitsLE (modulus c) + 1)) := by
  have h := congrArg
    (fun A : Matrix
      (Fin (FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c))))
      (Fin (FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c))))
      (Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1))) =>
        fun r s => PolynomialAffineDeformation.affine (A r s) (if r = s then 1 else 0))
    (original_matrix_reduction source active modulus inner middle n d ell B c)
  exact h.trans (deformation_reduction (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c) + 1)))
    (encodedRows source active B.degree n d ell c) (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (TubeCleared.matrixWidth (source c))).symm

theorem family_value_encoded (source active modulus inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) :
    (modularFamily source active modulus inner middle outer n d ell B).value c =
      IntegerBits.coefficientResidue
        (((encodedDeterminant source active B.degree n d ell c).coeff (Nat.fromBitsLE (outer c))).coeff
          (Nat.fromBitsLE (inner c) + radix source B.degree c * Nat.fromBitsLE (middle c)))
        (Nat.fromBitsLE (modulus c) + 1) := by
  change residueBits ((((modularFamily source active modulus inner middle outer n d ell B).matrix c).det.coeff
    (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (inner c) + radix source B.degree c * Nat.fromBitsLE (middle c))) = _
  have h := congrArg
    (fun A : Matrix
      (Fin (FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c))))
      (Fin (FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c))))
      (Polynomial (Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1)))) =>
        residueBits ((A.det.coeff (Nat.fromBitsLE (outer c))).coeff
          (Nat.fromBitsLE (inner c) + radix source B.degree c * Nat.fromBitsLE (middle c))))
    (affine_matrix_reduction source active modulus inner middle outer n d ell B c)
  change residueBits ((((modularFamily source active modulus inner middle outer n d ell B).matrix c).det.coeff
    (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (inner c) + radix source B.degree c * Nat.fromBitsLE (middle c))) = _ at h
  apply Eq.trans h
  change residueBits ((((encodedMatrix source active B.degree n d ell c).map (TubeBivariate.reduction (Nat.fromBitsLE (modulus c) + 1))).det.coeff
    (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (inner c) + radix source B.degree c * Nat.fromBitsLE (middle c))) = _
  have hm : ((encodedMatrix source active B.degree n d ell c).map (TubeBivariate.reduction (Nat.fromBitsLE (modulus c) + 1))).det =
      TubeBivariate.reduction (Nat.fromBitsLE (modulus c) + 1) (encodedMatrix source active B.degree n d ell c).det :=
    (RingHom.map_det (R := Polynomial (Polynomial ℤ)) (S := Polynomial (Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1))))
      (TubeBivariate.reduction (Nat.fromBitsLE (modulus c) + 1)) _).symm
  rw [hm, TubeBivariate.reduction_polynomial_coefficient]
  rfl

theorem family_value (source active modulus inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool)
    (hi : Nat.fromBitsLE (inner c) < radix source B.degree c) :
    (modularFamily source active modulus inner middle outer n d ell B).value c =
      IntegerBits.coefficientResidue (coefficient source active inner middle outer n d ell c) (Nat.fromBitsLE (modulus c) + 1) := by
  rw [family_value_encoded, coefficient_recovery source active n d ell B c _ _ _ hi]
  rfl

theorem coefficient_zero_of_not_lt (source active inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool)
    (hi : ¬Nat.fromBitsLE (inner c) < radix source B.degree c) : coefficient source active inner middle outer n d ell c = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have hd := determinant_inner_degree source active n d ell B c (Nat.fromBitsLE (outer c)) (Nat.fromBitsLE (middle c))
  unfold radix at hi
  omega

end LeanCanny.ETR.TubeDeformation

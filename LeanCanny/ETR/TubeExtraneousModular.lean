/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeExtraneousSystem
public import LeanCanny.Algebra.PolynomialPrincipalSpace

/-! # The full tube extraneous family as a modular principal deformation -/

@[expose] public section

namespace LeanCanny.ETR.TubeExtraneous
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open Algebra.RationalSubstitution Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det residueBits

noncomputable def family (source active modulus inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) : BerkowitzAffinePolynomial.Family :=
  (TubeDeformation.modularFamily source active modulus inner middle outer n d ell B).principal (indices source)

theorem selection_packet (source active modulus inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool)
    (r t : Fin ((TubeDeformation.originalFamily source active modulus inner middle n d ell B).dimension c)) (k : ℕ) :
    MacaulayBits.extraneousEntry (TubeCleared.layout source) (PolynomialAffineEntryBits.packet c r.val t.val k) ↔ r ∈ indices source c := by
  exact MacaulayBits.extraneousEntry_packet (TubeCleared.layout source) c r t.val k

noncomputable def access (source active modulus inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) :
    BerkowitzAffinePolynomial.Access (family source active modulus inner middle outer n d ell B) :=
  (TubeDeformation.modularAccess source active modulus inner middle outer n d ell B).principal
    (indices source) (MacaulayBits.extraneousEntry (TubeCleared.layout source))
    (selection_packet source active modulus inner middle n d ell B)

theorem family_matrix_reduction (source active modulus inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) :
    (family source active modulus inner middle outer n d ell B).matrix c =
      (encodedMatrix source active B.degree n d ell c).map (TubeBivariate.reduction (Nat.fromBitsLE (modulus c) + 1)) := by
  have hp := (TubeDeformation.modularFamily source active modulus inner middle outer n d ell B).principal_matrix (indices source) c
  have hm := congrArg
    (fun A : Matrix
      (Fin (FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c))))
      (Fin (FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c))))
      (Polynomial (Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1)))) => PrincipalPadding.matrix A (indices source c))
    (TubeDeformation.affine_matrix_reduction source active modulus inner middle outer n d ell B c)
  exact hp.trans (hm.trans (PrincipalPadding.matrix_map (TubeBivariate.reduction (Nat.fromBitsLE (modulus c) + 1))
    (TubeDeformation.encodedMatrix source active B.degree n d ell c) (indices source c)).symm)

theorem family_value_encoded (source active modulus inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) :
    (family source active modulus inner middle outer n d ell B).value c = IntegerBits.coefficientResidue
      (((encodedDeterminant source active B.degree n d ell c).coeff (Nat.fromBitsLE (outer c))).coeff
        (Nat.fromBitsLE (inner c) + TubeDeformation.radix source B.degree c * Nat.fromBitsLE (middle c)))
      (Nat.fromBitsLE (modulus c) + 1) := by
  change residueBits ((((family source active modulus inner middle outer n d ell B).matrix c).det.coeff
    (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (inner c) + TubeDeformation.radix source B.degree c * Nat.fromBitsLE (middle c))) = _
  have h := congrArg
    (fun A : Matrix
      (Fin (FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c))))
      (Fin (FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c))))
      (Polynomial (Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1)))) => residueBits ((A.det.coeff (Nat.fromBitsLE (outer c))).coeff
        (Nat.fromBitsLE (inner c) + TubeDeformation.radix source B.degree c * Nat.fromBitsLE (middle c))))
    (family_matrix_reduction source active modulus inner middle outer n d ell B c)
  change residueBits ((((family source active modulus inner middle outer n d ell B).matrix c).det.coeff
    (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (inner c) + TubeDeformation.radix source B.degree c * Nat.fromBitsLE (middle c))) = _ at h
  apply Eq.trans h
  have hm : ((encodedMatrix source active B.degree n d ell c).map (TubeBivariate.reduction (Nat.fromBitsLE (modulus c) + 1))).det =
      TubeBivariate.reduction (Nat.fromBitsLE (modulus c) + 1) (encodedMatrix source active B.degree n d ell c).det :=
    (RingHom.map_det (R := Polynomial (Polynomial ℤ)) (S := Polynomial (Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1))))
      (TubeBivariate.reduction (Nat.fromBitsLE (modulus c) + 1)) _).symm
  rw [hm, TubeBivariate.reduction_polynomial_coefficient]
  rfl

theorem family_value (source active modulus inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool)
    (hi : Nat.fromBitsLE (inner c) < TubeDeformation.radix source B.degree c) :
    (family source active modulus inner middle outer n d ell B).value c =
      IntegerBits.coefficientResidue (coefficient source active inner middle outer n d ell c) (Nat.fromBitsLE (modulus c) + 1) := by
  rw [family_value_encoded, coefficient_recovery source active n d ell B c _ _ _ hi]
  rfl

end LeanCanny.ETR.TubeExtraneous

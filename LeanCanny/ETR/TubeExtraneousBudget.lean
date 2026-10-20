/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeExtraneousSystem
public import LeanCanny.Algebra.MacaulayExtraneousBounds

/-! # Integer coefficient budgets for the full tube extraneous deformation

The original numerator budget also bounds the identity-padded principal
minor. All three parameters remain independent, and requests beyond the
perturbation radix have zero coefficient.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeExtraneous
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree TubeBivariate.rowMassCode

theorem coefficient_bits (source active read inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (c : List Bool) : (coefficient source active inner middle outer n d ell c).natAbs.size ≤ Nat.fromBitsLE (TubeDeformation.budget source read B.degree B.bits c) := by
  by_cases hi : Nat.fromBitsLE (inner c) < TubeDeformation.radix source B.degree c
  · unfold coefficient
    rw [← coefficient_recovery source active n d ell B c (Nat.fromBitsLE (inner c)) (Nat.fromBitsLE (outer c)) (Nat.fromBitsLE (middle c)) hi]
    rw [TubeDeformation.budget_code]
    apply Macaulay.extraneous_polynomial_deformation_coefficient_size (TubeDeformation.encodedRows source active B.degree n d ell c) _ _
      (Nat.fromBitsLE (TubeDeformation.entryDegreeCode source B.degree c)) _ (TubeDeformation.encoded_row_degree source active n d ell B c)
    intro i e
    rw [TubeDeformation.encodedRows, MvPolynomial.coeff_map]
    exact TubeBivariate.encoded_row_mass source active read n d ell B hr c _ i e
  · have hd := determinant_inner_degree source active n d ell B c (Nat.fromBitsLE (outer c)) (Nat.fromBitsLE (middle c))
    have hz : (((determinant source active n d ell c).coeff (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (middle c))).coeff
        (Nat.fromBitsLE (inner c)) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      unfold TubeDeformation.radix at hi
      omega
    simp only [coefficient, hz, Int.natAbs_zero, Nat.size_zero, Nat.zero_le]

end LeanCanny.ETR.TubeExtraneous

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeExtraneousBudget
public import LeanCanny.ETR.TubeDeformationCoefficientPolynomial

/-! # Finite scalar access to each tube extraneous deformation coefficient polynomial

The first parameter encoding preserves zero and has a uniform binary degree
allowance. Quotient/remainder scalar queries recover its coefficients exactly.
These facts permit identity testing without materializing either polynomial.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeExtraneous
open LeanCanny.Encoding LeanCanny.Algebra

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree Macaulay.matrix Matrix.det

noncomputable def scalarCoefficient (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (i j k : ℕ) : ℤ :=
  (((determinant source active n d ell c).coeff k).coeff j).coeff i

theorem coefficient_reindex (source active f inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (q : List Bool) :
    coefficient (source ∘ f) (active ∘ f) inner middle outer
      (fun c => n (f c)) (fun c => d (f c)) (fun c => ell (f c)) q =
      scalarCoefficient source active n d ell (f q) (Nat.fromBitsLE (inner q)) (Nat.fromBitsLE (middle q)) (Nat.fromBitsLE (outer q)) := rfl

theorem encoded_coefficient_degree (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) (k : ℕ) :
    ((encodedDeterminant source active B.degree n d ell c).coeff k).natDegree < Nat.fromBitsLE (TubeDeformation.coefficientCount source B.degree c) := by
  rw [TubeDeformation.coefficientCount_code, MacaulayBits.fromBits_encode]
  exact (Macaulay.extraneous_polynomial_deformation_inner_degree (TubeDeformation.encodedRows source active B.degree n d ell c) _ _ _
    (TubeDeformation.encoded_row_degree source active n d ell B c) k).trans_lt (Nat.lt_succ_self _)

theorem encoded_coefficient_zero_iff (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) (k : ℕ) :
    (encodedDeterminant source active B.degree n d ell c).coeff k = 0 ↔ (determinant source active n d ell c).coeff k = 0 := by
  rw [encodedDeterminant_eq_map, Polynomial.coeff_map]
  exact PolynomialKronecker.encode_eq_zero_iff _ _ (fun j => (determinant_inner_degree source active n d ell B c k j).trans_lt
    (Nat.lt_succ_self _))

theorem encoded_coefficient_any (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) (k u : ℕ) :
    ((encodedDeterminant source active B.degree n d ell c).coeff k).coeff u =
      scalarCoefficient source active n d ell c (u % TubeDeformation.radix source B.degree c) (u / TubeDeformation.radix source B.degree c) k := by
  rw [encodedDeterminant_eq_map, Polynomial.coeff_map]
  exact PolynomialKronecker.coefficient_any _ (Nat.succ_pos _) _
    (fun j => (determinant_inner_degree source active n d ell B c k j).trans_lt (Nat.lt_succ_self _)) u

end LeanCanny.ETR.TubeExtraneous

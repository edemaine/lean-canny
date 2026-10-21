/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationBudget

/-! # Finite scalar access to each tube deformation coefficient polynomial

The first parameter encoding preserves zero and has a uniform binary degree
allowance. Quotient/remainder scalar queries recover its coefficients exactly.
These facts permit identity testing without materializing either polynomial.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
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

noncomputable def coefficientCount (source degree : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.succ (BinaryNat.mul (pair (MacaulayBits.dimensionCode (TubeCleared.layout source) c) (entryDegreeCode source degree c)))

theorem coefficientCount_mem_FP {source degree : List Bool → List Bool} (hs : source ∈ FP) (hd : degree ∈ FP) : coefficientCount source degree ∈ FP := by
  have h := mem_FP_comp (mem_FP_comp (mem_FP_pair (MacaulayBits.dimensionCode_mem_FP (TubeCleared.layout_polyTime hs))
    (entryDegreeCode_mem_FP hs hd)) BinaryNat.mul_mem_FP) BinaryNat.succ_mem_FP
  exact mem_FP_of_eq (g := coefficientCount source degree) h (fun _ => by simp only [coefficientCount, Function.comp_apply])

theorem coefficientCount_code (source degree : List Bool → List Bool) (c : List Bool) :
    coefficientCount source degree c = BinaryNatCode.encode
      (FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) *
        Nat.fromBitsLE (entryDegreeCode source degree c) + 1) := by
  simp only [coefficientCount, MacaulayBits.dimensionCode, FixedWidthPolynomial.countCode_code,
    BinaryNat.mul_pair, MacaulayBits.fromBits_encode, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
  rfl

theorem encoded_coefficient_degree (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) (k : ℕ) :
    ((encodedDeterminant source active B.degree n d ell c).coeff k).natDegree < Nat.fromBitsLE (coefficientCount source B.degree c) := by
  rw [coefficientCount_code, MacaulayBits.fromBits_encode]
  exact (Macaulay.det_polynomial_deformation_inner_degree (encodedRows source active B.degree n d ell c) _ _ _
    (encoded_row_degree source active n d ell B c) k).trans_lt (Nat.lt_succ_self _)

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
      scalarCoefficient source active n d ell c (u % radix source B.degree c) (u / radix source B.degree c) k := by
  rw [encodedDeterminant_eq_map, Polynomial.coeff_map]
  exact PolynomialKronecker.coefficient_any _ (Nat.succ_pos _) _
    (fun j => (determinant_inner_degree source active n d ell B c k j).trans_lt (Nat.lt_succ_self _)) u

end LeanCanny.ETR.TubeDeformation

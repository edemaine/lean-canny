/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationSystem
public import LeanCanny.Algebra.MacaulayPolynomialDeformationBounds

/-! # Integer coefficient budgets for the full three-parameter deformation

The first encoding packs perturbation and projection while preserving their
coefficients. The independent affine deformation increases the encoded source
mass budget by two bits. Every original three-parameter integer coefficient
therefore has an FP determinant budget, including out-of-range inner requests.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree TubeBivariate.rowMassCode

theorem original_row_outer_degree (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (i : Fin (TubeParameter.spatialCount (source c)))
    (e : Fin (TubeParameter.spatialCount (source c)) →₀ ℕ) :
    ((TubeBivariate.rows source active n d ell c i).coeff e).natDegree ≤ 1 := by
  rw [TubeBivariate.rows]
  split_ifs
  · rw [MvPolynomial.coeff_map]
    change (((TubeLinear.polynomial source ell c).coeff e).map Polynomial.C).natDegree ≤ 1
    apply Polynomial.natDegree_map_le.trans
    apply LinearCoefficientBits.coefficient_natDegree_le
    intro j _
    rw [TubeLinear.scalar]
    split_ifs <;> simp
  · rw [MvPolynomial.coeff_map]
    simp

noncomputable def entryDegreeCode (source degree : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (TubeCleared.uniformDegree source degree c) (radixCode source degree c))

theorem entryDegreeCode_mem_FP {source degree : List Bool → List Bool} (hs : source ∈ FP) (hd : degree ∈ FP) :
    entryDegreeCode source degree ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (TubeCleared.uniformDegree_mem_FP hs hd) (radixCode_mem_FP hs hd)) BinaryNat.add_mem_FP
  exact mem_FP_of_eq (g := entryDegreeCode source degree) h (fun _ => by simp only [entryDegreeCode, Function.comp_apply])

theorem entryDegreeCode_value (source degree : List Bool → List Bool) (c : List Bool) :
    Nat.fromBitsLE (entryDegreeCode source degree c) = Nat.fromBitsLE (TubeCleared.uniformDegree source degree c) + radix source degree c := by
  simp only [entryDegreeCode, BinaryNat.add_pair, radixCode_code, MacaulayBits.fromBits_encode, Nat.fromBitsLE_bits]

theorem encoded_row_degree (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool)
    (i : Fin (TubeParameter.spatialCount (source c))) (e : Fin (TubeParameter.spatialCount (source c)) →₀ ℕ) :
    ((encodedRows source active B.degree n d ell c i).coeff e).natDegree ≤ Nat.fromBitsLE (entryDegreeCode source B.degree c) := by
  rw [encodedRows, MvPolynomial.coeff_map, entryDegreeCode_value]
  have h := PolynomialKronecker.encode_natDegree_le (radix source B.degree c)
    (Nat.fromBitsLE (TubeCleared.uniformDegree source B.degree c)) 1 ((TubeBivariate.rows source active n d ell c i).coeff e)
    (TubeBivariate.rows_inner_bound source active n d ell B c i e) (original_row_outer_degree source active n d ell c i e)
  simpa only [Nat.mul_one] using h

noncomputable def rowBudget (source read degree bits : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (TubeBivariate.rowMassCode source read degree bits c) (BinaryNatCode.encode 2))

theorem rowBudget_mem_FP {source read degree bits : List Bool → List Bool}
    (hs : source ∈ FP) (hr : read ∈ FP) (hd : degree ∈ FP) (hb : bits ∈ FP) : rowBudget source read degree bits ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (TubeBivariate.rowMassCode_mem_FP hs hr hd hb) (constFn_mem_FP (BinaryNatCode.encode 2))) BinaryNat.add_mem_FP
  exact mem_FP_of_eq (g := rowBudget source read degree bits) h (fun _ => by simp only [rowBudget, Function.comp_apply])

noncomputable def budget (source read degree bits : List Bool → List Bool) : List Bool → List Bool :=
  MacaulayBits.budgetCode (TubeCleared.layout source) (rowBudget source read degree bits)

theorem budget_mem_FP {source read degree bits : List Bool → List Bool}
    (hs : source ∈ FP) (hr : read ∈ FP) (hd : degree ∈ FP) (hb : bits ∈ FP) : budget source read degree bits ∈ FP :=
  MacaulayBits.budgetCode_mem_FP (TubeCleared.layout_polyTime hs) (rowBudget_mem_FP hs hr hd hb)

theorem budget_code (source read degree bits : List Bool → List Bool) (c : List Bool) :
    Nat.fromBitsLE (budget source read degree bits c) =
      (FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c))).size *
        FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) +
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) *
        (Nat.fromBitsLE (TubeBivariate.rowMassCode source read degree bits c) + 2) + 1 := by
  have h := MacaulayBits.budgetCode_code (TubeCleared.layout source) (rowBudget source read degree bits)
    (fun c => Nat.fromBitsLE (TubeBivariate.rowMassCode source read degree bits c) + 2)
    (by intro c; simp only [rowBudget, BinaryNat.add_pair, MacaulayBits.fromBits_encode]; rfl) c
  rw [budget, h, MacaulayBits.fromBits_encode]
  rfl

noncomputable def coefficient (source active inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : ℤ :=
  ((((determinant source active n d ell c).coeff (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (middle c))).coeff (Nat.fromBitsLE (inner c)))

theorem coefficient_bits (source active read inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (c : List Bool) : (coefficient source active inner middle outer n d ell c).natAbs.size ≤ Nat.fromBitsLE (budget source read B.degree B.bits c) := by
  by_cases hi : Nat.fromBitsLE (inner c) < radix source B.degree c
  · unfold coefficient
    rw [← coefficient_recovery source active n d ell B c (Nat.fromBitsLE (inner c)) (Nat.fromBitsLE (outer c)) (Nat.fromBitsLE (middle c)) hi]
    rw [budget_code]
    apply Macaulay.det_polynomial_deformation_coefficient_size_le (encodedRows source active B.degree n d ell c) _ _
      (Nat.fromBitsLE (entryDegreeCode source B.degree c)) _ (encoded_row_degree source active n d ell B c)
    intro i e
    rw [encodedRows, MvPolynomial.coeff_map]
    exact TubeBivariate.encoded_row_mass source active read n d ell B hr c _ i e
  · have hd := determinant_inner_degree source active n d ell B c (Nat.fromBitsLE (outer c)) (Nat.fromBitsLE (middle c))
    have hz : (((determinant source active n d ell c).coeff (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (middle c))).coeff
        (Nat.fromBitsLE (inner c)) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      unfold radix at hi
      omega
    simp only [coefficient, hz, Int.natAbs_zero, Nat.size_zero, Nat.zero_le]

end LeanCanny.ETR.TubeDeformation

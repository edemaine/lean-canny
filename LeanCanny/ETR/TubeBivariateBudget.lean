/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeClearedBudget
public import LeanCanny.ETR.TubeDirectionBounds
public import LeanCanny.Algebra.LinearCoefficientBounds
public import LeanCanny.Algebra.MacaulayBivariateBounds

/-! # Integer budgets for actual full regular tube determinant coefficients

Encoding the projection variable changes monomial positions but not the scalar
allowances. Regular coefficients use their uniform clearing budget; the linear
row uses the actual direction reader's output lengths. These supply an FP binary
bit budget for every selected integer bivariate determinant coefficient.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeBivariate
open LeanCanny.Encoding LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree TubeCleared.massBudget

noncomputable def projectionMap (B : ℕ) : Polynomial ℤ →+* Polynomial ℤ :=
  (PolynomialKronecker.encode B).comp (Polynomial.mapRingHom Polynomial.C)

theorem projectionMap_X (B : ℕ) : projectionMap B Polynomial.X = (Polynomial.X : Polynomial ℤ) ^ B := by
  simp only [projectionMap, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, PolynomialKronecker.encode_X]

theorem projectionMap_C (B : ℕ) (z : ℤ) : projectionMap B (Polynomial.C z) = Polynomial.C z := by
  simp only [projectionMap, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, PolynomialKronecker.encode_C]

theorem projection_scalar_mass (source read : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (c : List Bool) (i B : ℕ) (hi : i < TubeParameter.spatialCount (source c)) :
    coefficientMass (projectionMap B (TubeLinear.scalar ell c i)) ≤ 2 ^ directionSize source read c := by
  rw [TubeLinear.scalar]
  split_ifs
  · rw [projectionMap_X, coefficientMass_X_pow]
    exact Nat.one_le_two_pow
  · rw [map_neg, projectionMap_C, coefficientMass_neg, coefficientMass_C]
    exact direction_entry_bound source read ell hr c i hi

theorem projection_coefficient_mass (source read : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (c : List Bool) (B : ℕ) (e : Fin (TubeParameter.spatialCount (source c)) →₀ ℕ) :
    coefficientMass (projectionMap B ((TubeLinear.polynomial source ell c).coeff e)) ≤
      2 ^ ((TubeParameter.spatialCount (source c)).size + directionSize source read c) := by
  have h := LinearCoefficientBits.coefficient_mass_le (TubeParameter.spatialCount ∘ source) (TubeLinear.scalar ell) c (projectionMap B)
    (2 ^ directionSize source read c) (fun i hi => projection_scalar_mass source read ell hr c i B hi) e
  apply h.trans
  calc
    TubeParameter.spatialCount (source c) * 2 ^ directionSize source read c ≤
        2 ^ (TubeParameter.spatialCount (source c)).size * 2 ^ directionSize source read c :=
      Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
    _ = _ := (pow_add _ _ _).symm

noncomputable def rowMassCode (source read degree bits : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (TubeCleared.massBudget source degree bits c)
    (BinaryNatCode.encode ((TubeParameter.spatialCount (source c)).size + directionSize source read c)))

theorem rowMassCode_mem_FP {source read degree bits : List Bool → List Bool}
    (hs : source ∈ FP) (hr : read ∈ FP) (he : degree ∈ FP) (hb : bits ∈ FP) : rowMassCode source read degree bits ∈ FP := by
  have hlin := bits_mem_FP (((TubeParameter.spatialCount_unary.comp hs).size).add (directionSize_unary hs hr))
  have h := mem_FP_comp (mem_FP_pair (TubeCleared.massBudget_mem_FP hs he hb) hlin) BinaryNat.add_mem_FP
  exact mem_FP_of_eq (g := rowMassCode source read degree bits) h (fun _ => by simp only [rowMassCode, Function.comp_apply, BinaryNatCode.encode])

theorem rowMassCode_value (source read degree bits : List Bool → List Bool) (c : List Bool) :
    Nat.fromBitsLE (rowMassCode source read degree bits c) = Nat.fromBitsLE (TubeCleared.massBudget source degree bits c) +
      ((TubeParameter.spatialCount (source c)).size + directionSize source read c) := by
  simp only [rowMassCode, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem encoded_row_mass (source active read : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (c : List Bool) (r : ℕ) (i : Fin (TubeParameter.spatialCount (source c)))
    (e : Fin (TubeParameter.spatialCount (source c)) →₀ ℕ) :
    coefficientMass (PolynomialKronecker.encode r ((rows source active n d ell c i).coeff e)) ≤
      2 ^ Nat.fromBitsLE (rowMassCode source read B.degree B.bits c) := by
  rw [rows]
  split_ifs
  · rw [MvPolynomial.coeff_map]
    change coefficientMass (projectionMap r ((TubeLinear.polynomial source ell c).coeff e)) ≤ _
    apply (projection_coefficient_mass source read ell hr c r e).trans
    apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    rw [rowMassCode_value]
    omega
  · rw [MvPolynomial.coeff_map, PolynomialKronecker.encode_C]
    apply (TubeCleared.renamed_coefficient_mass source active _ n d B c e).trans
    apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    rw [rowMassCode_value]
    omega

noncomputable def integerMatrix (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) :=
  Macaulay.matrix (rows source active n d ell c) (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (TubeCleared.matrixWidth (source c))

noncomputable def integerCoefficient (source active inner outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : ℤ :=
  (((integerMatrix source active n d ell c).det.coeff (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (inner c)))

noncomputable def integerBudget (source read degree bits : List Bool → List Bool) : List Bool → List Bool :=
  MacaulayBits.budgetCode (TubeCleared.layout source) (BinaryNat.normalize ∘ rowMassCode source read degree bits)

theorem integerBudget_mem_FP {source read degree bits : List Bool → List Bool}
    (hs : source ∈ FP) (hr : read ∈ FP) (he : degree ∈ FP) (hb : bits ∈ FP) : integerBudget source read degree bits ∈ FP :=
  MacaulayBits.budgetCode_mem_FP (TubeCleared.layout_polyTime hs)
    (mem_FP_comp (rowMassCode_mem_FP hs hr he hb) BinaryNat.normalize_mem_FP)

theorem integerBudget_code (source read degree bits : List Bool → List Bool) (c : List Bool) :
    Nat.fromBitsLE (integerBudget source read degree bits c) =
      (FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c))).size *
        FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) +
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) *
        Nat.fromBitsLE (rowMassCode source read degree bits c) + 1 := by
  have h := MacaulayBits.budgetCode_code (TubeCleared.layout source)
    (BinaryNat.normalize ∘ rowMassCode source read degree bits) (fun c => Nat.fromBitsLE (rowMassCode source read degree bits c))
    (fun c => BinaryNat.normalize_eq_bits _) c
  rw [integerBudget, h, MacaulayBits.fromBits_encode]
  rfl

theorem integerCoefficient_bits (source active read inner outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (c : List Bool) :
    (integerCoefficient source active inner outer n d ell c).natAbs.size ≤ Nat.fromBitsLE (integerBudget source read B.degree B.bits c) := by
  rw [integerBudget_code]
  exact Macaulay.det_bivariate_coefficient_size_le (rows source active n d ell c) _ _
    (Nat.fromBitsLE (TubeCleared.uniformDegree source B.degree c)) _
    (rows_inner_bound source active n d ell B c) (fun r i e => encoded_row_mass source active read n d ell B hr c r i e) _ _

end LeanCanny.ETR.TubeBivariate

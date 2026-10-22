/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeBivariateSign
public import LeanCanny.Algebra.MacaulayDeformationParameters

/-! # Nonzero deformation of the full parameterized tube determinant

The inner variable is the perturbation parameter, the middle variable is the
projection value, and the outer variable is the deformation parameter. At
deformation zero the determinant is the original candidate; at one it is one.
A bounded coefficient encoding preserves the first two variables independently
while leaving the deformation variable untouched.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
open LeanCanny.Encoding LeanCanny.Algebra

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree

noncomputable def system (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) :=
  Macaulay.deformation (TubeBivariate.rows source active n d ell c) (MacaulayBits.Degrees (TubeCleared.layout source) c)

noncomputable def matrix (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) :=
  Macaulay.matrix (system source active n d ell c) (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (TubeCleared.matrixWidth (source c))

noncomputable def determinant (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) : Polynomial (Polynomial (Polynomial ℤ)) :=
  (matrix source active n d ell c).det

theorem system_homogeneous (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (i : Fin (TubeParameter.spatialCount (source c))) :
    (system source active n d ell c i).IsHomogeneous ((TubeCleared.layout source).degree c i.val) :=
  Macaulay.deformation_homogeneous _ _ (TubeBivariate.rows_homogeneous source active n d ell c) i

theorem determinant_at_zero (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    (determinant source active n d ell c).eval 0 = (TubeBivariate.integerMatrix source active n d ell c).det :=
  Macaulay.det_deformation_eval_zero _ _ _

theorem determinant_at_one (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) : (determinant source active n d ell c).eval 1 = 1 :=
  Macaulay.det_deformation_eval_one _ _ _

theorem determinant_ne_zero (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) : determinant source active n d ell c ≠ 0 :=
  Macaulay.det_deformation_ne_zero _ _ _

theorem determinant_degree (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    (determinant source active n d ell c).natDegree ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) :=
  Macaulay.det_deformation_degree_le _ _ _

theorem determinant_inner_degree (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) (j k : ℕ) :
    (((determinant source active n d ell c).coeff j).coeff k).natDegree ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) *
        Nat.fromBitsLE (TubeCleared.uniformDegree source B.degree c) :=
  Macaulay.det_deformation_inner_degree _ _ _ _ (TubeBivariate.rows_inner_bound source active n d ell B c) j k

noncomputable def radix (source degree : List Bool → List Bool) (c : List Bool) : ℕ :=
  FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) *
    Nat.fromBitsLE (TubeCleared.uniformDegree source degree c) + 1

noncomputable def radixCode (source degree : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.succ (BinaryNat.mul (pair (MacaulayBits.dimensionCode (TubeCleared.layout source) c) (TubeCleared.uniformDegree source degree c)))

theorem radixCode_mem_FP {source degree : List Bool → List Bool} (hs : source ∈ FP) (hd : degree ∈ FP) : radixCode source degree ∈ FP := by
  have hM := MacaulayBits.dimensionCode_mem_FP (TubeCleared.layout_polyTime hs)
  have h := mem_FP_comp (mem_FP_comp (mem_FP_pair hM (TubeCleared.uniformDegree_mem_FP hs hd)) BinaryNat.mul_mem_FP) BinaryNat.succ_mem_FP
  exact mem_FP_of_eq (g := radixCode source degree) h (fun _ => by simp only [radixCode, Function.comp_apply])

theorem radixCode_code (source degree : List Bool → List Bool) (c : List Bool) :
    radixCode source degree c = BinaryNatCode.encode (radix source degree c) := by
  simp only [radixCode, MacaulayBits.dimensionCode, FixedWidthPolynomial.countCode_code, BinaryNat.succ_eq_bits,
    BinaryNat.mul_pair, MacaulayBits.fromBits_encode, Nat.fromBitsLE_bits]
  rfl

noncomputable def encodedRows (source active degree : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) :=
  fun i => (TubeBivariate.rows source active n d ell c i).map (PolynomialKronecker.encode (radix source degree c))

noncomputable def encodedDeterminant (source active degree : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) : Polynomial (Polynomial ℤ) :=
  (Macaulay.matrix (Macaulay.deformation (encodedRows source active degree n d ell c) (MacaulayBits.Degrees (TubeCleared.layout source) c))
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))).det

theorem encodedDeterminant_eq_map (source active degree : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    encodedDeterminant source active degree n d ell c =
      (determinant source active n d ell c).map (PolynomialKronecker.encode (radix source degree c)) :=
  (Macaulay.det_deformation_map _ _ _ _).symm

theorem encodedDeterminant_ne_zero (source active degree : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) : encodedDeterminant source active degree n d ell c ≠ 0 :=
  Macaulay.det_deformation_ne_zero _ _ _

theorem coefficient_recovery (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) (i j k : ℕ)
    (hi : i < radix source B.degree c) :
    ((encodedDeterminant source active B.degree n d ell c).coeff j).coeff (i + radix source B.degree c * k) =
      (((determinant source active n d ell c).coeff j).coeff k).coeff i := by
  rw [encodedDeterminant_eq_map, Polynomial.coeff_map]
  exact PolynomialKronecker.coefficient _ _ (fun k => (determinant_inner_degree source active n d ell B c j k).trans_lt
    (Nat.lt_succ_self _)) i k hi

end LeanCanny.ETR.TubeDeformation

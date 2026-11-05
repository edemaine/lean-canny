/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantPackingLayout
public import LeanCanny.Algebra.MacaulayPaddedValueParameterDegree
public import LeanCanny.Algebra.MacaulayFixedPaddedPolynomialValue
public import LeanCanny.Algebra.FixedWidthKronecker
/-! # Exact Kronecker packing of the actual normalized formal eliminant

The radix is derived from the original syntax and full native matrix dimension.
It accommodates the entire normalized output, not only the input rows.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantPacked
open LeanCanny.Algebra LeanCanny.Connectivity MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open FormulaSignSlotRadialEliminantPackingLayout
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] MacaulayUniversal.polynomialValue

noncomputable def system (c : List Bool) (row : Fin (spatial c + 1)) :=
  (FormulaSignSlotRadialEliminantParameterRows.row (pairFst c)
    (FormulaSignSlotRadialEliminantInput.coordinate c) row).map
      (FixedWidthKronecker.encode (d (pairFst c) + 3) (parameterWidth c))

noncomputable def eliminant (c : List Bool) :=
  FixedWidthKronecker.encode (d (pairFst c) + 3) (parameterWidth c)
    (FormulaSignSlotRadialEliminantParameterRows.eliminant (pairFst c)
      (FormulaSignSlotRadialEliminantInput.coordinate c))

noncomputable def parameterBox (c : List Bool) :=
  FixedWidthPolynomial.count (d (pairFst c) + 3) (parameterWidth c)

theorem parameterBox_binary : BinaryFn parameterBox := by
  have H := (BinaryFn.const 2).powUnary
    ((parameterWidth_unary).mul ((FormulaSignSlotSource.dimension_unary.comp pairFst_mem_FP).add (UnaryFn.const 3)))
  exact H.of_eq (fun c => by
    simp only [parameterBox, FixedWidthPolynomial.count, ← pow_mul])

theorem row_support (c : List Bool) (row : Fin (spatial c + 1))
    (e : Fin (spatial c + 1) →₀ ℕ)
    (f : Fin (d (pairFst c) + 3) →₀ ℕ)
    (hf : f ∈ ((FormulaSignSlotRadialEliminantParameterRows.row (pairFst c)
      (FormulaSignSlotRadialEliminantInput.coordinate c) row).coeff e).support)
    (i : Fin (d (pairFst c) + 3)) : f i < 2 ^ parameterWidth c :=
  ((monomial_le_degreeOf i hf).trans ((degreeOf_le_totalDegree _ i).trans
    (FormulaSignSlotRadialEliminantParameterSupport.degree_bound (pairFst c) _ _ _))).trans_lt (parameter_fit c)

theorem coefficient (c : List Bool) (row : Fin (spatial c + 1))
    (e : Fin (spatial c + 1) →₀ ℕ) (k : Fin (parameterBox c)) :
    (((system c row).coeff e).coeff k.val) =
      ((FormulaSignSlotRadialEliminantParameterRows.row (pairFst c)
        (FormulaSignSlotRadialEliminantInput.coordinate c) row).coeff e).coeff
          (FixedWidthPolynomial.vector (d (pairFst c) + 3) (parameterWidth c) k) := by
  rw [system, coeff_map]
  exact FixedWidthKronecker.coefficient _ _ _ (row_support c row e) k

theorem coefficient_of_ge (c : List Bool) (row : Fin (spatial c + 1))
    (e : Fin (spatial c + 1) →₀ ℕ) (k : ℕ) (hk : parameterBox c ≤ k) :
    (((system c row).coeff e).coeff k) = 0 := by
  rw [system, coeff_map]
  exact FixedWidthKronecker.coefficient_of_ge _ _ _ (row_support c row e) k hk

theorem coefficient_degree (c : List Bool) (row : Fin (spatial c + 1))
    (e : Fin (spatial c + 1) →₀ ℕ) : ((system c row).coeff e).natDegree ≤ parameterBox c := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  exact coefficient_of_ge c row e k hk.le

theorem homogeneous (c : List Bool) (row : Fin (spatial c + 1)) :
    (system c row).IsHomogeneous (CoerciveCriticalHomogenization.finDegree (sourceDegree c) row) :=
  (FormulaSignSlotRadialEliminantParameterRows.homogeneous (pairFst c) _ row).map _

theorem polynomialValue (c : List Bool) :
    MacaulayUniversal.polynomialValue (CoerciveCriticalHomogenization.finDegree (sourceDegree c))
      (width c) (CoerciveCoordinateEliminant.degree_lt _ _) (CoerciveCoordinateEliminant.level_lt _ _)
      (system c) = eliminant c := by
  have H := MacaulayUniversal.polynomialValue_map
    (FixedWidthKronecker.encode (d (pairFst c) + 3) (parameterWidth c))
    (CoerciveCriticalHomogenization.finDegree (sourceDegree c)) (width c)
    (CoerciveCoordinateEliminant.degree_lt _ _) (CoerciveCoordinateEliminant.level_lt _ _)
    (FormulaSignSlotRadialEliminantParameterRows.row (pairFst c) (FormulaSignSlotRadialEliminantInput.coordinate c))
  have HV := FormulaSignSlotRadialEliminantParameterRows.polynomialValue (pairFst c)
    (FormulaSignSlotRadialEliminantInput.coordinate c)
  have HH := congrArg (FixedWidthKronecker.encode (d (pairFst c) + 3) (parameterWidth c)) HV
  exact H.symm.trans HH

noncomputable def resultDegree (c : List Bool) := (columns c + 1) * (columns c * parameterDegree c)

theorem result_degree (c : List Bool) :
    (FormulaSignSlotRadialEliminantParameterRows.eliminant (pairFst c)
      (FormulaSignSlotRadialEliminantInput.coordinate c)).totalDegree ≤ resultDegree c := by
  have H := MacaulayPaddedValueParameterDegree.normalized_value
    (FormulaSignSlotRadialEliminantParameterRows.row (pairFst c) (FormulaSignSlotRadialEliminantInput.coordinate c))
    (CoerciveCriticalHomogenization.finDegree (sourceDegree c)) (width c) (parameterDegree c)
    (CoerciveCoordinateEliminant.degree_lt _ _) (CoerciveCoordinateEliminant.level_lt _ _)
    (FormulaSignSlotRadialEliminantParameterRows.homogeneous (pairFst c) _)
    (CoerciveCriticalHomogenization.finDegree_pos _)
    (FormulaSignSlotRadialEliminantParameterSupport.degree_bound (pairFst c) _)
  have HV := congrArg MvPolynomial.totalDegree
    (FormulaSignSlotRadialEliminantParameterRows.polynomialValue (pairFst c)
      (FormulaSignSlotRadialEliminantInput.coordinate c))
  have HBound := HV.symm.le.trans H
  have HR := MacaulayFixedPaddedPolynomialValue.reduced_le_dimension
    (CoerciveCriticalHomogenization.finDegree (sourceDegree c)) (width c)
    (CoerciveCriticalHomogenization.finDegree_pos _) (CoerciveCoordinateEliminant.level_lt _ _)
  exact HBound.trans (Nat.mul_le_mul_right _ (Nat.succ_le_succ HR))

theorem result_fit (c : List Bool) : resultDegree c < 2 ^ parameterWidth c := by
  have HN := columns_pos c
  have HE : parameterDegree c < 2 ^ (parameterDegree c + 2) :=
    (Nat.lt_add_of_pos_right (by decide)).trans Nat.lt_two_pow_self
  calc
    resultDegree c ≤ (2 * columns c) * (columns c * parameterDegree c) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ (2 * columnExponent c + 1) * parameterDegree c := by rw [columns_eq]; ring
    _ < 2 ^ (2 * columnExponent c + 1) * 2 ^ (parameterDegree c + 2) :=
      Nat.mul_lt_mul_of_pos_left HE (Nat.two_pow_pos _)
    _ = 2 ^ parameterWidth c := by
      rw [← pow_add]
      congr 1
      unfold parameterWidth
      omega

theorem eliminant_coefficient (c : List Bool) (k : Fin (parameterBox c)) :
    (eliminant c).coeff k.val =
      (FormulaSignSlotRadialEliminantParameterRows.eliminant (pairFst c)
        (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff
          (FixedWidthPolynomial.vector (d (pairFst c) + 3) (parameterWidth c) k) := by
  apply FixedWidthKronecker.coefficient
  intro f hf i
  exact ((monomial_le_degreeOf i hf).trans ((degreeOf_le_totalDegree _ i).trans
    (result_degree c))).trans_lt (result_fit c)

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantPacked

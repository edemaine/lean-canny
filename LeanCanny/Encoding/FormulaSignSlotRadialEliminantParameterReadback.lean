/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterQuery
/-! # Every field of the packed parameter query has its literal exponent -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterQuery
open LeanCanny.Algebra LeanCanny.Connectivity MvPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem block_eq_entry (V : ℕ) (word : List Bool) (i : ℕ) :
    Nat.fromBitsLE ((word.drop (i * V)).take V) =
      FixedWidthPolynomial.entry V (Nat.fromBitsLE word) i := by
  rw [FixedWidthPolynomial.entry_eq_digit, BinaryNat.value_take, FixedWidthPolynomial.drop_value]

private theorem queryEntry_lt (A W : List Bool → ℕ) (target : List Bool → List Bool)
    (q : List Bool) (i : ℕ) : FixedWidthQuery.entry A W target q i < 2 ^ W q := by
  unfold FixedWidthQuery.entry FixedWidthQuery.coordinate
  split_ifs
  · exact (Nat.fromBitsLE_lt_pow_length _).trans_le
      (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))
  · exact Nat.two_pow_pos _

private theorem queryEntry_eq (A W : List Bool → ℕ) (target : List Bool → List Bool)
    (q : List Bool) (i : ℕ) (hi : i < A q) :
    FixedWidthQuery.entry A W target q i = FixedWidthPolynomial.entry (W q) (Nat.fromBitsLE (target q)) i := by
  rw [FixedWidthQuery.entry, ite_eq_left hi]
  exact block_eq_entry _ _ _

theorem sourceEntry_lt (q : List Bool) (i : ℕ) : sourceEntry q i < 2 ^ sourceWidth q := by
  unfold sourceEntry
  split_ifs
  · exact (queryEntry_lt _ _ _ q _).trans_le (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  · exact (queryEntry_lt _ _ _ q _).trans_le (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  · exact (queryEntry_lt _ _ _ q _).trans_le (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  · exact Nat.two_pow_pos _

theorem sourceWord_coordinate (q : List Bool) (i : ℕ) (hi : i < sourceDimension q) :
    FixedWidthPolynomial.entry (sourceWidth q) (Nat.fromBitsLE (sourceWord q)) i = sourceEntry q i := by
  rw [← block_eq_entry]
  exact FixedWidthNatVector.decode_block _ _ _ i hi (sourceEntry_lt q i)

noncomputable def original (q : List Bool) := pairFst (context q)
noncomputable def sourceExponent (q : List Bool) :=
  FormulaSignSlotRadialEliminantCoefficientNative.sourceExponent original sourceWidth sourceWord q
noncomputable def spatialExponent (q : List Bool) :=
  FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (spatial q + 1)))
    (macroWidth q) (Nat.fromBitsLE (spatialWord q))
noncomputable def parameterExponent (q : List Bool) :=
  FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (parameterDimension q)))
    (parameterWidth q) (Nat.fromBitsLE (parameterWord q))
noncomputable def headWord (q : List Bool) := (spatialWord q).take (macroWidth q)
noncomputable def epsilonWord (q : List Bool) := (parameterWord q).take (parameterWidth q)
noncomputable def targetWord (q : List Bool) := ((parameterWord q).drop (parameterWidth q)).take (parameterWidth q)

local instance radialParameterQueryDimensionNeZero (q : List Bool) : NeZero (parameterDimension q) := ⟨by unfold parameterDimension; omega⟩

attribute [local irreducible] sourceEntry sourceDimension sourceWord macroWidth parameterWidth sourceWidth

theorem dimension_eq (q : List Bool) : FormulaSignSlotRadialFormalInput.dimension (original q) = sourceDimension q := by
  unfold FormulaSignSlotRadialFormalInput.dimension original sourceDimension spatial
    FormulaSignSlotRadialEliminantPackingLayout.spatial centers
  exact (Nat.add_assoc _ _ _).symm

theorem original_FP : original ∈ FP := mem_FP_comp context_FP pairFst_mem_FP
theorem headWord_FP : headWord ∈ FP := take_mem_FP spatialWord_FP macroWidth_unary
theorem epsilonWord_FP : epsilonWord ∈ FP := take_mem_FP parameterWord_FP parameterWidth_unary
theorem targetWord_FP : targetWord ∈ FP :=
  take_mem_FP (drop_mem_FP parameterWord_FP parameterWidth_unary) parameterWidth_unary

theorem sourceExponent_apply (q : List Bool) (i : Fin (FormulaSignSlotRadialFormalInput.dimension (original q))) :
    sourceExponent q i = sourceEntry q i.val := by
  change FixedWidthPolynomial.entry (sourceWidth q) (Nat.fromBitsLE (sourceWord q)) i.val = _
  exact sourceWord_coordinate q i.val (i.isLt.trans_eq (dimension_eq q))

theorem spatial_readback (q : List Bool) (i : Fin (spatial q)) :
    FormulaSignSlotRadialEliminantCoefficientQuery.spatial (original q) (sourceExponent q) i =
      FixedWidthPolynomial.entry (macroWidth q) (Nat.fromBitsLE (spatialWord q)) (i.val + 1) := by
  change sourceExponent q (FormulaSignSlotRadialFormalInput.spatialIndex (original q) i) = _
  have H := sourceExponent_apply q (FormulaSignSlotRadialFormalInput.spatialIndex (original q) i)
  have HC : sourceEntry q i.val = FixedWidthPolynomial.entry (macroWidth q)
      (Nat.fromBitsLE (spatialWord q)) (i.val + 1) := by
    rw [sourceEntry, ite_eq_left i.isLt]
    exact queryEntry_eq _ _ _ q _ (by have := i.isLt; omega)
  have HI : (FormulaSignSlotRadialFormalInput.spatialIndex (original q) i).val = i.val := by
    simp only [FormulaSignSlotRadialFormalInput.spatialIndex, Fin.val_castAdd]
  exact H.trans ((congrArg (sourceEntry q) HI).trans HC)

theorem center_readback (q : List Bool) (i : Fin (centers q)) :
    FormulaSignSlotRadialEliminantCoefficientQuery.center (original q) (sourceExponent q) i =
      FixedWidthPolynomial.entry (parameterWidth q) (Nat.fromBitsLE (parameterWord q)) (i.val + 3) := by
  change sourceExponent q (FormulaSignSlotRadialFormalInput.formalCenterIndex (original q) i) = _
  rw [sourceExponent_apply]
  change sourceEntry q (spatial q + i.val) = _
  rw [sourceEntry, ite_eq_right (by omega), ite_eq_left (by have := i.isLt; omega), Nat.add_sub_cancel_left]
  exact queryEntry_eq _ _ _ q _ (by have := i.isLt; unfold parameterDimension; omega)

theorem radius_readback (q : List Bool) :
    FormulaSignSlotRadialEliminantCoefficientQuery.radius (original q) (sourceExponent q) =
      FixedWidthPolynomial.entry (parameterWidth q) (Nat.fromBitsLE (parameterWord q)) 2 := by
  change sourceExponent q (FormulaSignSlotRadialFormalInput.formalRadiusIndex (original q)) = _
  rw [sourceExponent_apply]
  change sourceEntry q (spatial q + centers q) = _
  rw [sourceEntry, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  exact queryEntry_eq _ _ _ q _ (by unfold parameterDimension; omega)

theorem head_readback (q : List Bool) :
    Nat.fromBitsLE (headWord q) = spatialExponent q 0 := by
  change Nat.fromBitsLE ((spatialWord q).take (macroWidth q)) =
    FixedWidthPolynomial.entry (macroWidth q) (Nat.fromBitsLE (spatialWord q)) 0
  simpa only [Nat.zero_mul, List.drop_zero] using block_eq_entry (macroWidth q) (spatialWord q) 0

theorem epsilon_readback (q : List Bool) : Nat.fromBitsLE (epsilonWord q) = parameterExponent q 0 := by
  change Nat.fromBitsLE ((parameterWord q).take (parameterWidth q)) =
    FixedWidthPolynomial.entry (parameterWidth q) (Nat.fromBitsLE (parameterWord q)) 0
  simpa only [Nat.zero_mul, List.drop_zero] using block_eq_entry (parameterWidth q) (parameterWord q) 0

theorem target_readback (q : List Bool) : Nat.fromBitsLE (targetWord q) = (parameterExponent q).tail 0 := by
  change Nat.fromBitsLE (((parameterWord q).drop (parameterWidth q)).take (parameterWidth q)) =
    FixedWidthPolynomial.entry (parameterWidth q) (Nat.fromBitsLE (parameterWord q)) 1
  simpa only [Nat.one_mul] using block_eq_entry (parameterWidth q) (parameterWord q) 1

theorem radius_parameter (q : List Bool) :
    FormulaSignSlotRadialEliminantCoefficientQuery.radius (original q) (sourceExponent q) =
      (parameterExponent q).tail.tail 0 := radius_readback q

theorem center_parameter (q : List Bool) :
    FormulaSignSlotRadialEliminantCoefficientQuery.center (original q) (sourceExponent q) =
      (parameterExponent q).tail.tail.tail := by
  ext i
  exact center_readback q i

theorem homogeneous_readback (q : List Bool) :
    (FormulaSignSlotRadialEliminantCoefficientNative.homogeneousExponent original sourceWidth sourceWord headWord q).mapDomain
      CoerciveCriticalHomogenization.layout = spatialExponent q := by
  have HE : FormulaSignSlotRadialEliminantCoefficientNative.homogeneousExponent original sourceWidth sourceWord headWord q =
      FixedWidthPolynomial.nativeExponent (CoerciveCriticalHomogenization.layout (n := spatial q))
        (macroWidth q) (Nat.fromBitsLE (spatialWord q)) := by
    ext i
    cases i with
    | none =>
      dsimp only [FormulaSignSlotRadialEliminantCoefficientNative.homogeneousExponent,
        FormulaSignSlotRadialEliminantCoefficientQuery.homogeneous]
      rw [Finsupp.optionElim_apply_none]
      change Nat.fromBitsLE (headWord q) =
        FixedWidthPolynomial.entry (macroWidth q) (Nat.fromBitsLE (spatialWord q)) 0
      exact head_readback q
    | some i =>
      dsimp only [FormulaSignSlotRadialEliminantCoefficientNative.homogeneousExponent,
        FormulaSignSlotRadialEliminantCoefficientQuery.homogeneous]
      rw [Finsupp.optionElim_apply_some]
      change FormulaSignSlotRadialEliminantCoefficientQuery.spatial (original q) (sourceExponent q) i =
        FixedWidthPolynomial.entry (macroWidth q) (Nat.fromBitsLE (spatialWord q)) (i.val + 1)
      exact spatial_readback q i
  rw [HE, FixedWidthPolynomial.nativeExponent_map]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterQuery

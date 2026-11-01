/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualNativeDerivative
public import LeanCanny.Algebra.IntegralMixedVirtualNativeFolds
public import LeanCanny.Algebra.IntegralMixedVirtualFactorModel
public import LeanCanny.Algebra.IntegralMixedVirtualGridModel
/-! # Canonical residue witnesses for actual virtual lower models -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualCanonicalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

theorem empty_canonical (m : ℕ) : ∃ z : ZMod m, residueBits z = [] := ⟨0, (ArithmeticBits.zero_residueBits m).symm⟩
theorem entryBits_canonical {m n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod m)) (r t : ℕ) :
    ∃ z : ZMod m, residueBits z = IntegralCriticalActualLowMatrixModel.entryBits M r t := by
  unfold IntegralCriticalActualLowMatrixModel.entryBits
  split_ifs
  · exact ⟨_, rfl⟩
  all_goals exact empty_canonical m

theorem original_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualNativeLowerBits.original P F q := by
  rw [IntegralMixedVirtualCoefficientBits.original_snapshot]
  unfold IntegralMixedVirtualCoefficientBits.originalAt
  exact ⟨_, rfl⟩
theorem derivative_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualCoefficientBits.derivative P F q := by
  unfold IntegralMixedVirtualCoefficientBits.derivative IntegralMixedVirtualCoefficientBits.derivativeAt
  exact ⟨_, rfl⟩
theorem height_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualNativeLowerBits.height P F q := by
  rw [IntegralMixedVirtualNativeLowerBits.height_eq]
  exact ⟨_, rfl⟩
theorem monomial_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualFactorBits.monomial P F q := by
  unfold IntegralMixedVirtualFactorBits.monomial
  rw [IntegralMixedVirtualFactorBits.factor_snapshot]
  exact entryBits_canonical _ _ _
theorem power_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualFactorBits.power P F q := by
  unfold IntegralMixedVirtualFactorBits.power
  rw [IntegralMixedVirtualFactorBits.power_snapshot]
  exact entryBits_canonical _ _ _
theorem product_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualGridBits.product P F q := by
  unfold IntegralMixedVirtualGridBits.product IntegralMonomialTermBits.Source.value
  rw [IntegralMixedVirtualGridBits.source_modulus]
  exact ⟨_, rfl⟩
theorem term_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualGridBits.term P F q := by
  rw [IntegralMixedVirtualGridBits.term_as_product]
  split_ifs
  · exact product_canonical P F q
  · exact empty_canonical _
theorem cleared_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualSpatialBits.cleared P F q := by
  unfold IntegralMixedVirtualSpatialBits.cleared IntegralClearedCoefficientBits.Source.value
  exact ⟨_, rfl⟩

theorem frozenTerm_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualSnapshotBits.frozenTerm P F q := by
  unfold IntegralMixedVirtualSnapshotBits.frozenTerm
  rw [IntegralFrozenPowerBits.term_packet]
  exact ⟨_, rfl⟩
theorem frozenSum_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualSnapshotBits.frozenSum P F q := by
  rw [IntegralMixedVirtualSnapshotBits.frozenSum_eq]
  unfold IntegralFrozenPowerBits.Source.sumValue
  exact ⟨_, rfl⟩
theorem frozenConstant_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualSnapshotBits.frozenConstant P F q := by
  rw [IntegralMixedVirtualSnapshotBits.frozenConstant_eq]
  unfold IntegralFrozenPowerBits.Source.constantValue
  exact ⟨_, rfl⟩
theorem frozenLower_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualSnapshotBits.frozenLower P F q := by
  rw [IntegralMixedVirtualSnapshotBits.frozenLower_eq]
  unfold IntegralFrozenPowerBits.Source.lowerValue
  exact ⟨_, rfl⟩
theorem coordinateProduct_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualFoldBits.product P F q := by
  rw [IntegralMixedVirtualFoldBits.product_eq_term, IntegralEulerBits.term_packet]
  exact ⟨_, rfl⟩
theorem sum_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualSnapshotBits.sum P F q := by
  rw [IntegralMixedVirtualSnapshotBits.sum_eq]
  unfold IntegralEulerBits.Source.sumValue
  exact ⟨_, rfl⟩
theorem objective_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualSnapshotBits.objective P F q := by
  rw [IntegralMixedVirtualSnapshotBits.objective_eq]
  unfold IntegralEulerBits.Source.objectiveValue
  exact ⟨_, rfl⟩
theorem lower_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualSnapshotBits.lower P F q := by
  rw [IntegralMixedVirtualSnapshotBits.lower_eq]
  unfold IntegralEulerBits.Source.lowerValue
  exact ⟨_, rfl⟩
theorem originalLeading_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualNativeLowerBits.originalLeadingValue P F q := ⟨_, rfl⟩
theorem commonLeading_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z =
      IntegralCriticalLeadingBits.value (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen q := ⟨_, rfl⟩
end LeanCanny.Algebra.IntegralMixedVirtualCanonicalBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualMonomialReplies
public import LeanCanny.Algebra.IntegralCriticalActualProductEntryTransport
public import LeanCanny.Algebra.IntegralCriticalActualGridTransport
public import LeanCanny.Algebra.IntegralCriticalActualProductModel
/-! # Canonical residue values of actual lower arithmetic stages -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualLowerCanonical
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

theorem empty_canonical (m : ℕ) : ∃ z : ZMod m, residueBits z = [] :=
  ⟨0, (ArithmeticBits.zero_residueBits m).symm⟩

theorem entryBits_canonical {m n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod m)) (r t : ℕ) :
    ∃ z : ZMod m, residueBits z = IntegralCriticalActualLowMatrixModel.entryBits M r t := by
  unfold IntegralCriticalActualLowMatrixModel.entryBits
  split_ifs
  · exact ⟨_, rfl⟩
  all_goals exact empty_canonical m

theorem original_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualCoefficientModel.original F q := by
  unfold IntegralCriticalActualCoefficientModel.original IntegralCriticalActualCoefficientModel.originalAt IntegralCriticalActualFactorModel.factorAt
  exact entryBits_canonical _ _ _

theorem derivative_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualCoefficientModel.derivative F q := by
  unfold IntegralCriticalActualCoefficientModel.derivative IntegralCriticalActualCoefficientModel.derivativeAt IntegralCriticalActualFactorModel.factorAt
  exact entryBits_canonical _ _ _

theorem height_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalTotalHeightBits.value F q := by
  unfold IntegralCriticalTotalHeightBits.value IntegralCriticalTotalHeightBits.entry
    IntegralHistoryCriticalBits.heightValue UniformIntegralPrefix.Prefix.elementEntry
  exact ⟨_, rfl⟩

theorem monomial_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualFactorModel.monomial F q := by
  unfold IntegralCriticalActualFactorModel.monomial
  rw [IntegralCriticalActualFactorModel.factor_snapshot]
  exact entryBits_canonical _ _ _

theorem power_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualFactorModel.power F q := by
  unfold IntegralCriticalActualFactorModel.power
  rw [IntegralCriticalActualFactorModel.power_snapshot]
  exact entryBits_canonical _ _ _

theorem productEntry_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualLowMatrixModel.productEntry F q := by
  unfold IntegralCriticalActualLowMatrixModel.productEntry
  rw [IntegralCriticalActualLowMatrixModel.layered_snapshot]
  exact entryBits_canonical _ _ _

theorem product_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualGridTransport.product F q := by
  unfold IntegralCriticalActualGridTransport.product IntegralMonomialTermBits.Source.value
  rw [IntegralCriticalFlatActualLow.source_modulus]
  exact ⟨_, rfl⟩

theorem term_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualGridTransport.term F q := by
  rw [IntegralCriticalActualGridTransport.term_as_product]
  split_ifs
  · exact product_canonical F q
  · exact empty_canonical _

theorem cleared_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualSpatialTransport.cleared F q := by
  unfold IntegralCriticalActualSpatialTransport.cleared IntegralClearedCoefficientBits.Source.value
  exact ⟨_, rfl⟩

theorem frozenTerm_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualScalarModels.frozenTerm F q := by
  rw [IntegralCriticalActualScalarModels.frozenTerm_eq]
  unfold IntegralCriticalFlatFrozenTermBits.input
  rw [IntegralFrozenPowerBits.term_packet]
  exact ⟨_, rfl⟩

theorem frozenSum_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualScalarModels.frozenSum F q := by
  rw [IntegralCriticalActualScalarModels.frozenSum_eq]
  unfold IntegralFrozenPowerBits.Source.sumValue
  exact ⟨_, rfl⟩

theorem frozenConstant_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualScalarModels.frozenConstant F q := by
  rw [IntegralCriticalActualScalarModels.frozenConstant_eq]
  unfold IntegralFrozenPowerBits.Source.constantValue
  exact ⟨_, rfl⟩

theorem frozenLower_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualScalarModels.frozenLower F q := by
  rw [IntegralCriticalActualScalarModels.frozenLower_eq]
  unfold IntegralFrozenPowerBits.Source.lowerValue
  exact ⟨_, rfl⟩

theorem sum_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualScalarModels.sum F q := by
  rw [IntegralCriticalActualScalarModels.sum_eq]
  unfold IntegralEulerBits.Source.sumValue
  exact ⟨_, rfl⟩

theorem objective_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualScalarModels.objective F q := by
  rw [IntegralCriticalActualScalarModels.objective_eq]
  unfold IntegralEulerBits.Source.objectiveValue
  exact ⟨_, rfl⟩

theorem lower_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualScalarModels.lower F q := by
  rw [IntegralCriticalActualScalarModels.lower_eq]
  unfold IntegralEulerBits.Source.lowerValue
  exact ⟨_, rfl⟩

theorem coordinateProduct_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = IntegralCriticalActualProductModel.product F q := by
  rw [IntegralCriticalActualProductModel.product_eq_term, IntegralEulerBits.term_packet]
  exact ⟨_, rfl⟩

end LeanCanny.Algebra.IntegralCriticalActualLowerCanonical

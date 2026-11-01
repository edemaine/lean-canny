/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualLowerCanonical
public import LeanCanny.Algebra.IntegralCriticalFlatActualReductionPower
public import LeanCanny.Algebra.IntegralCriticalFlatActualRawRelativeEntry
public import LeanCanny.Algebra.IntegralCriticalTotalMomentValueSnapshot
/-! # One canonical residue model for every flat critical-history phase -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualModelBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources
set_option backward.isDefEq.respectTransparency false

private theorem canonical_mod_eq {m n : ℕ} {w : List Bool} (hm : m = n)
    (hc : ∃ z : ZMod m, residueBits z = w) : ∃ z : ZMod n, residueBits z = w := by
  subst n
  exact hc

private theorem power_canonical (S : IntegralBlockPowerBits.Family) (q : List Bool) :
    ∃ z : ZMod (S.modulus q), residueBits z = S.value q := by
  unfold IntegralBlockPowerBits.Family.value
  exact ⟨_, rfl⟩

private theorem moment_canonical (S : IntegralBlockMomentBits.Family) (q : List Bool) :
    ∃ z : ZMod (S.modulus q), residueBits z = S.value q := by
  unfold IntegralBlockMomentBits.Family.value
  exact ⟨_, rfl⟩

private theorem reduction_modulus (F : Scripts) (q : List Bool) :
    (reduction F).modulus q = IntegralCriticalHistoryTask.modulus F.toParameters q := rfl

attribute [local irreducible] relative reduction characteristic IntegralCriticalTotalCreatingBits.atFamily

theorem reductionEntry_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q),
      residueBits z = IntegralCriticalFlatActualReductionEntryBits.value F q := by
  unfold IntegralCriticalFlatActualReductionEntryBits.value IntegralCriticalTotalSnapshotBits.modularReductionEntry
  exact ⟨_, rfl⟩

theorem reductionPower_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q),
      residueBits z = IntegralCriticalTotalActionSnapshotBits.powerValue F q := by
  have HM : (IntegralCriticalFlatReductionPowerBits.family F.toParameters (reduction F)).modulus q =
      IntegralCriticalHistoryTask.modulus F.toParameters q :=
    (IntegralCriticalFlatActualReductionPowerBits.family_modulus F.toParameters (reduction F) q).trans (reduction_modulus F q)
  exact canonical_mod_eq HM (power_canonical (IntegralCriticalFlatReductionPowerBits.family F.toParameters (reduction F)) q)

theorem action_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q),
      residueBits z = IntegralCriticalFlatActualActionBits.value F q := by
  unfold IntegralCriticalFlatActualActionBits.value IntegralCriticalTotalSnapshotBits.modularActionEntry
  exact ⟨_, rfl⟩

theorem momentEntry_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q),
      residueBits z = IntegralCriticalFlatActualMomentBits.value F q := by
  unfold IntegralCriticalFlatActualMomentBits.value IntegralCriticalTotalMomentSnapshotBits.modularEntry
  exact ⟨_, rfl⟩

theorem trailingMoment_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q),
      residueBits z = IntegralCriticalTotalMomentValueSnapshotBits.value F q :=
  canonical_mod_eq (IntegralCriticalFlatActualMomentBits.moment_modulus F q)
    (moment_canonical (IntegralCriticalFlatActualMomentBits.moment F) q)

theorem relativeFactor_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q),
      residueBits z = IntegralCriticalFlatActualRelativeFactorBits.value F q := by
  unfold IntegralCriticalFlatActualRelativeFactorBits.value IntegralCriticalTotalSnapshotBits.modularPowerEntry
  exact ⟨_, rfl⟩

theorem relativePower_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = (characteristic F).value q := by
  have H : ∃ z : ZMod ((characteristic F).modulus q), residueBits z = (characteristic F).value q := by
    unfold IntegralBerkowitzBlockBits.Source.value
    exact ⟨_, rfl⟩
  exact canonical_mod_eq (characteristic_modulus F q) H

theorem coefficient_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q),
      residueBits z = IntegralCriticalTotalCreatingBits.coefficientValue F q := by
  by_cases hv : IntegralCriticalTotalCompanionBits.valid F q
  · rw [IntegralCriticalTotalCreatingBits.coefficientValue_valid F q hv,
      IntegralCriticalTotalCompanionBits.coefficientValue, IntegralCriticalTotalCompanionBits.coefficientAt_creating F q hv]
    exact ⟨_, rfl⟩
  · rw [IntegralCriticalTotalCreatingBits.coefficientValue_invalid F q hv]
    exact IntegralCriticalActualLowerCanonical.empty_canonical _

theorem companion_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q),
      residueBits z = IntegralCriticalFlatHeightBits.companionValue F q := by
  unfold IntegralCriticalFlatHeightBits.companionValue
  split_ifs
  · unfold IntegralCriticalCreatingBits.value
    exact ⟨_, rfl⟩
  · exact IntegralCriticalActualLowerCanonical.empty_canonical _

noncomputable def component (F : Scripts) : Phase → List Bool → List Bool
  | .originalCoefficient => IntegralCriticalActualCoefficientModel.original F
  | .derivativeCoefficient => IntegralCriticalActualCoefficientModel.derivative F
  | .clearedHeight => IntegralCriticalTotalHeightBits.value F
  | .monomialFactor => IntegralCriticalActualFactorModel.monomial F
  | .factorPower => IntegralCriticalActualFactorModel.power F
  | .productEntry => IntegralCriticalActualLowMatrixModel.productEntry F
  | .productPower => IntegralCriticalActualGridTransport.product F
  | .originalGridTerm => IntegralCriticalActualGridTransport.term F
  | .clearedGridSum => IntegralCriticalActualSpatialTransport.cleared F
  | .frozenPowerTerm => IntegralCriticalActualScalarModels.frozenTerm F
  | .frozenPowerSum => IntegralCriticalActualScalarModels.frozenSum F
  | .frozenConstant => IntegralCriticalActualScalarModels.frozenConstant F
  | .frozenLower => IntegralCriticalActualScalarModels.frozenLower F
  | .coordinateGradientProduct => IntegralCriticalActualProductModel.product F
  | .eulerSum => IntegralCriticalActualScalarModels.sum F
  | .eulerObjective => IntegralCriticalActualScalarModels.objective F
  | .eulerLower => IntegralCriticalActualScalarModels.lower F
  | .reductionEntry => IntegralCriticalFlatActualReductionEntryBits.value F
  | .reductionPower => IntegralCriticalTotalActionSnapshotBits.powerValue F
  | .actionEntry => IntegralCriticalFlatActualActionBits.value F
  | .actionPower => fun _ => []
  | .momentEntry => IntegralCriticalFlatActualMomentBits.value F
  | .momentPower => IntegralCriticalTotalMomentValueSnapshotBits.value F
  | .relativeFactor => IntegralCriticalFlatActualRelativeFactorBits.value F
  | .relativePower => (characteristic F).value
  | .criticalCoefficient => IntegralCriticalTotalCreatingBits.coefficientValue F
  | .companion => IntegralCriticalFlatHeightBits.companionValue F

theorem component_canonical (F : Scripts) (p : Phase) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = component F p q := by
  cases p with
  | originalCoefficient => exact IntegralCriticalActualLowerCanonical.original_canonical F q
  | derivativeCoefficient => exact IntegralCriticalActualLowerCanonical.derivative_canonical F q
  | clearedHeight => exact IntegralCriticalActualLowerCanonical.height_canonical F q
  | monomialFactor => exact IntegralCriticalActualLowerCanonical.monomial_canonical F q
  | factorPower => exact IntegralCriticalActualLowerCanonical.power_canonical F q
  | productEntry => exact IntegralCriticalActualLowerCanonical.productEntry_canonical F q
  | productPower => exact IntegralCriticalActualLowerCanonical.product_canonical F q
  | originalGridTerm => exact IntegralCriticalActualLowerCanonical.term_canonical F q
  | clearedGridSum => exact IntegralCriticalActualLowerCanonical.cleared_canonical F q
  | frozenPowerTerm => exact IntegralCriticalActualLowerCanonical.frozenTerm_canonical F q
  | frozenPowerSum => exact IntegralCriticalActualLowerCanonical.frozenSum_canonical F q
  | frozenConstant => exact IntegralCriticalActualLowerCanonical.frozenConstant_canonical F q
  | frozenLower => exact IntegralCriticalActualLowerCanonical.frozenLower_canonical F q
  | coordinateGradientProduct => exact IntegralCriticalActualLowerCanonical.coordinateProduct_canonical F q
  | eulerSum => exact IntegralCriticalActualLowerCanonical.sum_canonical F q
  | eulerObjective => exact IntegralCriticalActualLowerCanonical.objective_canonical F q
  | eulerLower => exact IntegralCriticalActualLowerCanonical.lower_canonical F q
  | reductionEntry => exact reductionEntry_canonical F q
  | reductionPower => exact reductionPower_canonical F q
  | actionEntry => exact action_canonical F q
  | actionPower => exact IntegralCriticalActualLowerCanonical.empty_canonical _
  | momentEntry => exact momentEntry_canonical F q
  | momentPower => exact trailingMoment_canonical F q
  | relativeFactor => exact relativeFactor_canonical F q
  | relativePower => exact relativePower_canonical F q
  | criticalCoefficient => exact coefficient_canonical F q
  | companion => exact companion_canonical F q

def decode : ℕ → Phase
  | 0 => .originalCoefficient
  | 1 => .derivativeCoefficient
  | 2 => .clearedHeight
  | 3 => .monomialFactor
  | 4 => .factorPower
  | 5 => .productEntry
  | 6 => .productPower
  | 7 => .originalGridTerm
  | 8 => .clearedGridSum
  | 9 => .frozenPowerTerm
  | 10 => .frozenPowerSum
  | 11 => .frozenConstant
  | 12 => .frozenLower
  | 13 => .coordinateGradientProduct
  | 14 => .eulerSum
  | 15 => .eulerObjective
  | 16 => .eulerLower
  | 17 => .reductionEntry
  | 18 => .reductionPower
  | 19 => .actionEntry
  | 20 => .actionPower
  | 21 => .momentEntry
  | 22 => .momentPower
  | 23 => .relativeFactor
  | 24 => .relativePower
  | 25 => .criticalCoefficient
  | 26 => .companion
  | _ => .actionPower

theorem decode_code (p : Phase) : decode p.code = p := by cases p <;> rfl

noncomputable def value (F : Scripts) (q : List Bool) : List Bool :=
  if IntegralCriticalTotalCompanionBits.valid F q then component F (decode (phase q)) q else []

theorem value_canonical (F : Scripts) (q : List Bool) :
    ∃ z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q), residueBits z = value F q := by
  unfold value
  split_ifs
  · exact component_canonical F _ q
  · exact IntegralCriticalActualLowerCanonical.empty_canonical _

noncomputable def residue (F : Scripts) (q : List Bool) : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q) :=
  Classical.choose (value_canonical F q)

theorem residue_value (F : Scripts) (q : List Bool) : residueBits (residue F q) = value F q :=
  Classical.choose_spec (value_canonical F q)

theorem value_phase (F : Scripts) (p : Phase) (q : List Bool)
    (hv : IntegralCriticalTotalCompanionBits.valid F q) (hp : isPhase p q) : value F q = component F p q := by
  rw [value, ite_eq_left hv]
  change phase q = p.code at hp
  rw [hp, decode_code]

end LeanCanny.Algebra.IntegralCriticalActualModelBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeBranch
public import LeanCanny.Algebra.IntegralCriticalActualLowerCanonical
/-! # Actual lower-stage models and native task-writer matching -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

noncomputable def model (F : Scripts) : Phase → List Bool → List Bool
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
  | _ => fun _ => []

def Matches (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) : Prop :=
  ∀ p q, p.code ≤ 16 → IntegralCriticalTotalCompanionBits.valid F q → isPhase p q → answer F x q = model F p q

theorem valid_context (F : Scripts) (c q : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q)
    (hb : birth F.toParameters c = birth F.toParameters q)
    (hv : IntegralCriticalTotalCompanionBits.valid F q) : IntegralCriticalTotalCompanionBits.valid F c := by
  change birth F.toParameters c < (F.rules (RankedHistoryTask.root c)).length
  rw [hr, hb]
  exact hv

theorem matches_context (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (p : Phase) (hp : p.code ≤ 16) (c q : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q)
    (hb : birth F.toParameters c = birth F.toParameters q)
    (hv : IntegralCriticalTotalCompanionBits.valid F q) (hc : isPhase p c) : answer F x c = model F p c :=
  hm p c hp (valid_context F c q hr hb hv) hc

theorem matches_matrix (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (p : Phase) (hp : p.code ≤ 16) (z : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F (pairFst z)) :
    answer F x (IntegralCriticalFlatMatrixQuery.writer F.toParameters p z) = model F p (IntegralCriticalFlatMatrixQuery.writer F.toParameters p z) :=
  matches_context F x hm p hp _ (pairFst z) (IntegralCriticalFlatMatrixQuery.writer_root F.toParameters p z)
    (IntegralCriticalFlatMatrixQuery.writer_birth F.toParameters p z) hv (IntegralCriticalFlatMatrixQuery.writer_phase F.toParameters p z)

theorem matches_grid (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (p : Phase) (hp : p.code ≤ 16) (z : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F (pairFst z)) :
    answer F x (IntegralCriticalFlatGridBits.writer F.toParameters p z) = model F p (IntegralCriticalFlatGridBits.writer F.toParameters p z) :=
  matches_context F x hm p hp _ (pairFst z) (IntegralCriticalFlatGridBits.writer_root F.toParameters p z)
    (IntegralCriticalFlatGridBits.writer_birth F.toParameters p z) hv (IntegralCriticalFlatGridBits.writer_phase F.toParameters p z)

theorem matches_factor (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (p : Phase) (hp : p.code ≤ 16) (z : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F (pairFst z)) :
    answer F x (IntegralCriticalFlatFactorQuery.writer F.toParameters p z) = model F p (IntegralCriticalFlatFactorQuery.writer F.toParameters p z) :=
  matches_context F x hm p hp _ (pairFst z) (IntegralCriticalFlatFactorQuery.writer_root F.toParameters p z)
    (IntegralCriticalFlatFactorQuery.writer_birth F.toParameters p z) hv (IntegralCriticalFlatFactorQuery.writer_phase F.toParameters p z)

theorem matches_coordinate (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (p : Phase) (hp : p.code ≤ 16) (z : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F (pairFst z)) :
    answer F x (IntegralCriticalFlatCoordinateQuery.writer F.toParameters p z) = model F p (IntegralCriticalFlatCoordinateQuery.writer F.toParameters p z) :=
  matches_context F x hm p hp _ (pairFst z) (IntegralCriticalFlatCoordinateQuery.writer_root F.toParameters p z)
    (IntegralCriticalFlatCoordinateQuery.writer_birth F.toParameters p z) hv (IntegralCriticalFlatCoordinateQuery.writer_phase F.toParameters p z)

theorem matches_next (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (p : Phase) (hp : p.code ≤ 16) (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    answer F x (IntegralCriticalFlatEulerBits.next F.toParameters p q) = model F p (IntegralCriticalFlatEulerBits.next F.toParameters p q) :=
  matches_context F x hm p hp _ q (IntegralCriticalFlatEulerBits.next_root F.toParameters p q)
    (IntegralCriticalFlatEulerBits.next_birth F.toParameters p q) hv (IntegralCriticalFlatEulerBits.next_phase F.toParameters p q)

theorem matches_spatial (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (p : Phase) (hp : p.code ≤ 16) (e : ℕ) (z : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F (pairFst z)) :
    answer F x (IntegralCriticalFlatEulerRowsBits.spatial F.toParameters p e z) =
      model F p (IntegralCriticalFlatEulerRowsBits.spatial F.toParameters p e z) :=
  matches_context F x hm p hp _ (pairFst z) (IntegralCriticalFlatEulerRowsBits.spatial_root F.toParameters p e z)
    (IntegralCriticalFlatEulerRowsBits.spatial_birth F.toParameters p e z) hv (IntegralCriticalFlatEulerRowsBits.spatial_phase F.toParameters p e z)

theorem matches_derivative (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (z : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F (IntegralDerivativeBits.original z)) :
    answer F x (IntegralCriticalFlatDerivativeQuery.writer F.toParameters z) =
      model F .originalCoefficient (IntegralCriticalFlatDerivativeQuery.writer F.toParameters z) :=
  matches_context F x hm .originalCoefficient (by decide) _ (IntegralDerivativeBits.original z)
    (IntegralCriticalFlatDerivativeQuery.writer_root F.toParameters z)
    (IntegralCriticalFlatDerivativeQuery.writer_birth F.toParameters z) hv (IntegralCriticalFlatDerivativeQuery.writer_phase F.toParameters z)

end LeanCanny.Algebra.IntegralCriticalNativeLowerBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualLayeredCanonical
/-! # Canonical lower component models for the mixed routine graph -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualLowerModelBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false
noncomputable def component (P : Parameters) (F : Family) : Phase → List Bool → List Bool
  | .originalCoefficient => IntegralMixedVirtualNativeLowerBits.original P F
  | .derivativeCoefficient => IntegralMixedVirtualCoefficientBits.derivative P F
  | .clearedHeight => IntegralMixedVirtualNativeLowerBits.height P F
  | .monomialFactor => IntegralMixedVirtualFactorBits.monomial P F
  | .factorPower => IntegralMixedVirtualFactorBits.power P F
  | .productEntry => IntegralMixedVirtualLayeredBits.productEntry P F
  | .productPower => IntegralMixedVirtualGridBits.product P F
  | .originalGridTerm => IntegralMixedVirtualGridBits.term P F
  | .clearedGridSum => IntegralMixedVirtualSpatialBits.cleared P F
  | .frozenPowerTerm => IntegralMixedVirtualSnapshotBits.frozenTerm P F
  | .frozenPowerSum => IntegralMixedVirtualSnapshotBits.frozenSum P F
  | .frozenConstant => IntegralMixedVirtualSnapshotBits.frozenConstant P F
  | .frozenLower => IntegralMixedVirtualSnapshotBits.frozenLower P F
  | .coordinateGradientProduct => IntegralMixedVirtualFoldBits.product P F
  | .eulerSum => IntegralMixedVirtualSnapshotBits.sum P F
  | .eulerObjective => IntegralMixedVirtualSnapshotBits.objective P F
  | .eulerLower => IntegralMixedVirtualSnapshotBits.lower P F
  | _ => fun _ => []

theorem component_canonical (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = component P F p q := by
  cases p
  case originalCoefficient => exact IntegralMixedVirtualCanonicalBits.original_canonical P F q
  case derivativeCoefficient => exact IntegralMixedVirtualCanonicalBits.derivative_canonical P F q
  case clearedHeight => exact IntegralMixedVirtualCanonicalBits.height_canonical P F q
  case monomialFactor => exact IntegralMixedVirtualCanonicalBits.monomial_canonical P F q
  case factorPower => exact IntegralMixedVirtualCanonicalBits.power_canonical P F q
  case productEntry => exact IntegralMixedVirtualCanonicalBits.productEntry_canonical P F q
  case productPower => exact IntegralMixedVirtualCanonicalBits.product_canonical P F q
  case originalGridTerm => exact IntegralMixedVirtualCanonicalBits.term_canonical P F q
  case clearedGridSum => exact IntegralMixedVirtualCanonicalBits.cleared_canonical P F q
  case frozenPowerTerm => exact IntegralMixedVirtualCanonicalBits.frozenTerm_canonical P F q
  case frozenPowerSum => exact IntegralMixedVirtualCanonicalBits.frozenSum_canonical P F q
  case frozenConstant => exact IntegralMixedVirtualCanonicalBits.frozenConstant_canonical P F q
  case frozenLower => exact IntegralMixedVirtualCanonicalBits.frozenLower_canonical P F q
  case coordinateGradientProduct => exact IntegralMixedVirtualCanonicalBits.coordinateProduct_canonical P F q
  case eulerSum => exact IntegralMixedVirtualCanonicalBits.sum_canonical P F q
  case eulerObjective => exact IntegralMixedVirtualCanonicalBits.objective_canonical P F q
  case eulerLower => exact IntegralMixedVirtualCanonicalBits.lower_canonical P F q
  all_goals exact IntegralMixedVirtualCanonicalBits.empty_canonical _
end LeanCanny.Algebra.IntegralMixedVirtualLowerModelBits

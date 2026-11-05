/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFramedCoordinateRootSource
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightTransport

/-! # Planning preserves the complete explicit-key coordinate characteristic

The key is literal. Active/inactive births and invalid retained indices are
included; no equality of parsed arithmetic packets or caller words is used.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedNormalizationBits (planned plannedPlan plannedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool → ℕ)

theorem count_planned (c : List Bool) :
    count (planned P L F C) (plannedPlan P D L F C) (plannedData P D H L F C) c = count P D H c := rfl

theorem dimension_planned (c : List Bool) :
    dimension (planned P L F C) (plannedPlan P D L F C) (plannedData P D H L F C) c = dimension P D H c := rfl

theorem common_planned (c : List Bool) :
    common (planned P L F C) (plannedPlan P D L F C) (plannedData P D H L F C) c = common P D H c := rfl

theorem matrix_planned (c : List Bool) :
    matrix (planned P L F C) (plannedPlan P D L F C) (plannedData P D H L F C) c = matrix P D H c := by
  funext r t
  unfold matrix
  have HA : Active (planned P L F C) c = Active P c := rfl
  rw [HA]
  split_ifs
  · rw [IntegralMixedFramedOldHeightBankBits.sourceEntry_planned, count_planned]
  · rfl

theorem polynomial_planned (c : List Bool) :
    polynomial (planned P L F C) (plannedPlan P D L F C) (plannedData P D H L F C) c = polynomial P D H c := by
  rw [polynomial, matrix_planned, common_planned]
  rfl

end LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBits

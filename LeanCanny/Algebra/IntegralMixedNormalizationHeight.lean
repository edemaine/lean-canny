/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationCaps
public import LeanCanny.Algebra.CharacteristicIntegerBounds
/-! # Uniform characteristic bit budgets for actual normalization matrices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

def characteristicBudget (P : Parameters) (height : List Bool → ℕ) (r : List Bool) : ℕ :=
  CharacteristicIntegerBounds.budget (rankCap P r) (height r)

theorem characteristicBudget_binary (P : Parameters) (a : Access P) (height : List Bool → ℕ) (hh : BinaryFn height) :
    BinaryFn (characteristicBudget P height) :=
  CharacteristicIntegerBounds.budget_binary (rankCap_binary P a) hh

theorem coefficient_bits (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (height : List Bool → ℕ)
    (hh : ∀ q, IntegralMixedVirtualCaps.valid P q → ∀ i j,
      (top F (IntegralMixedVirtualTaskBits.saved P q) i j).natAbs ≤ 2 ^ height (RankedHistoryTask.root q))
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (k : ℕ) :
    ((top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.coeff k).natAbs.size ≤
      characteristicBudget P height (RankedHistoryTask.root q) := by
  have H := CharacteristicIntegerBounds.coefficient_bits (top F (IntegralMixedVirtualTaskBits.saved P q))
    (height (RankedHistoryTask.root q)) (hh q hv) k
  have HD := dimension_rankCap P F g q hv
  have HM : CharacteristicIntegerBounds.budget (dimension F (IntegralMixedVirtualTaskBits.saved P q))
      (height (RankedHistoryTask.root q)) ≤ characteristicBudget P height (RankedHistoryTask.root q) := by
    unfold characteristicBudget CharacteristicIntegerBounds.budget
    gcongr
    exact Nat.size_le_size HD
  exact H.trans HM

theorem zero_scan_cap (P : Parameters) (height : List Bool → ℕ)
    (hc : ∀ r, 2 * characteristicBudget P height r + 4 ≤ P.modulusBound r) (q : List Bool) :
    2 * characteristicBudget P height (RankedHistoryTask.root q) + 4 ≤ numericCap P (RankedHistoryTask.root q) :=
  (hc _).trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.2.2

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits

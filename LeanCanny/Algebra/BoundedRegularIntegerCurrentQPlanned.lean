/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.BoundedRegularIntegerCurrentQOriginal
/-! # Original-source current-Q controls with derived arithmetic budgets -/
@[expose] public section
namespace LeanCanny.Algebra.BoundedRegularIntegerCurrentQBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedNormalizationBits (planned plannedPlan plannedData planned_access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem represents_planned (P : Parameters) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents P D J T) (L F C : List Bool → ℕ) :
    IntegralMixedFramedHeaderBits.Represents (planned P L F C) (plannedPlan P D L F C) (plannedData P D J L F C) T :=
  ⟨hr.commands,hr.fallback⟩

theorem state_planned (P : Parameters) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ) (key : List Bool) :
    HEq ((IntegralMixedFramedHistoryFamilyBits.family (planned P L F C) (plannedPlan P D L F C)
      (plannedData P D J L F C)).state key) ((IntegralMixedFramedHistoryFamilyBits.family P D J).state key) := HEq.rfl

noncomputable def plannedControls (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Original P D J)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (L F C : List Bool → ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) :=
  controls (planned P L F C) (planned_access P a hL hF hC) (plannedPlan P D L F C) (plannedData P D J L F C)
    (s.planned L F C) T ht ⟨hr.commands,hr.fallback⟩ L F C hL hF hC

theorem plannedBounds (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Original P D J)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (L F C : List Bool → ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (hi : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hf : ∀root,1≤F root) (hl : ∀root,1≤L root) :
    IntegralMixedFramedCurrentQNativeBits.Bounds (planned P L F C) (plannedPlan P D L F C) (plannedData P D J L F C)
      (plannedControls P a D J s T ht hr L F C hL hF hC) where
  original:=IntegralMixedFramedNormalizationBits.planned_familyInputs P D L F C hi
  factor:=hf
  fallback:=IntegralMixedFramedZeroRulesBits.fallback_bounds _ _ _ (s.zero.planned L F C) L C hl
  modulus:=IntegralMixedFramedNormalizationBits.planned_budget P L F C

theorem planned_model_space (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Original P D J)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (L F C : List Bool → ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (hi : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hf : ∀root,1≤F root) (hl : ∀root,1≤L root) :
    SpaceFunction (IntegralMixedFramedCurrentQNativeBits.machine (planned P L F C) (planned_access P a hL hF hC)
      (plannedPlan P D L F C) (plannedData P D J L F C) (plannedControls P a D J s T ht hr L F C hL hF hC)).model :=
  IntegralMixedFramedCurrentQNativeBits.model_space _ _ _ _ _ (plannedBounds P a D J s T ht hr L F C hL hF hC hi hf hl)

end LeanCanny.Algebra.BoundedRegularIntegerCurrentQBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNativeSyntax
public import LeanCanny.Algebra.IntegralMixedFramedNormalizationPlanned
/-! # Derived height and modulus budgets for the full syntax-bound controller

Planning changes the packed query encoding. Original instructions, terms and
selector bodies retain their literal saved-key meaning; no equality of old
and new packed queries is claimed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedNormalizationBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem physical_rule_planned (P : Parameters) (D : Plan P) (L F C : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedPhysicalBits.rule (IntegralMixedFramedNormalizationBits.planned P L F C) (plannedPlan P D L F C) key =
      IntegralMixedFramedPhysicalBits.rule P D key := by
  cases hc : (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;>
    simp only [IntegralMixedFramedPhysicalBits.rule,planned_instruction,hc] <;> rfl

private theorem virtual_rule_planned (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family (IntegralMixedFramedNormalizationBits.planned P L F C)
      (plannedPlan P D L F C) (plannedData P D H L F C)).rule key =
        (IntegralMixedFramedHistoryFamilyBits.family P D H).rule key := by
  cases hc : (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;>
    simp only [IntegralMixedFramedHistoryFamilyBits.family,IntegralMixedFramedHistoryFamilyBits.selection,
      planned_instruction,plannedData,hc]

private theorem integer_planned (P : Parameters) (D : Plan P) (L F C : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial (IntegralMixedFramedNormalizationBits.planned P L F C) (plannedPlan P D L F C) key =
      IntegralMixedFramedIntegerBits.polynomial P D key := by
  cases hc : (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;>
    simp only [IntegralMixedFramedIntegerBits.polynomial,planned_instruction,hc]

noncomputable def Syntax.planned (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Syntax P D H) :
    Syntax (IntegralMixedFramedNormalizationBits.planned P s.nodes s.factor s.seed)
      (plannedPlan P D s.nodes s.factor s.seed) (plannedData P D H s.nodes s.factor s.seed) where
  unit := {
    tables := s.unit.tables
    native := s.unit.native
    represents := ⟨s.unit.represents.commands,s.unit.represents.fallback⟩
    writer := s.unit.writer
    writer_FP := s.unit.writer_FP
    snapshot := {
      leading := s.unit.snapshot.leading
      physicalScales key i := by
        change (IntegralMixedFramedPhysicalBits.rule (IntegralMixedFramedNormalizationBits.planned P s.nodes s.factor s.seed) (plannedPlan P D s.nodes s.factor s.seed) key).scales i = _
        rw [physical_rule_planned]
        exact s.unit.snapshot.physicalScales key i
      virtualScales key i := by
        change ((IntegralMixedFramedHistoryFamilyBits.family (IntegralMixedFramedNormalizationBits.planned P s.nodes s.factor s.seed) (plannedPlan P D s.nodes s.factor s.seed) (plannedData P D H s.nodes s.factor s.seed)).rule key).critical.scales i = _
        rw [virtual_rule_planned]
        exact s.unit.snapshot.virtualScales key i
      physicalHeights key i := by
        change (IntegralMixedFramedPhysicalBits.rule (IntegralMixedFramedNormalizationBits.planned P s.nodes s.factor s.seed) (plannedPlan P D s.nodes s.factor s.seed) key).heights i = _
        rw [physical_rule_planned]
        exact s.unit.snapshot.physicalHeights key i
      virtualHeights key i := by
        change ((IntegralMixedFramedHistoryFamilyBits.family (IntegralMixedFramedNormalizationBits.planned P s.nodes s.factor s.seed) (plannedPlan P D s.nodes s.factor s.seed) (plannedData P D H s.nodes s.factor s.seed)).rule key).critical.heights i = _
        rw [virtual_rule_planned]
        exact s.unit.snapshot.virtualHeights key i
      height key := by
        change ((IntegralMixedFramedHistoryFamilyBits.family (IntegralMixedFramedNormalizationBits.planned P s.nodes s.factor s.seed) (plannedPlan P D s.nodes s.factor s.seed) (plannedData P D H s.nodes s.factor s.seed)).rule key).height.val = _
        rw [virtual_rule_planned]
        exact s.unit.snapshot.height key
      slope key := by
        change ((IntegralMixedFramedHistoryFamilyBits.family (IntegralMixedFramedNormalizationBits.planned P s.nodes s.factor s.seed) (plannedPlan P D s.nodes s.factor s.seed) (plannedData P D H s.nodes s.factor s.seed)).rule key).slope = _
        rw [virtual_rule_planned]
        exact s.unit.snapshot.slope key } }
  term := s.term
  frozen := s.frozen
  tilt := s.tilt
  exponent := s.exponent
  term_FP := s.term_FP
  frozen_native := s.frozen_native
  tilt_native := s.tilt_native
  exponent_native := s.exponent_native
  term_scope := s.term_scope
  tilt_scope := s.tilt_scope
  low := s.low
  integerWord := s.integerWord
  integer_FP := s.integer_FP
  integer key := by
    exact (s.integer key).trans (integer_planned P D s.nodes s.factor s.seed key).symm
  nodes := s.nodes
  factor := s.factor
  seed := s.seed
  nodes_native := s.nodes_native
  factor_native := s.factor_native
  seed_native := s.seed_native

noncomputable def plannedControls (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Syntax P D H) :=
  Controls.ofSyntax (IntegralMixedFramedNormalizationBits.planned P s.nodes s.factor s.seed)
    (planned_access P a s.nodes_native s.factor_native s.seed_native)
    (plannedPlan P D s.nodes s.factor s.seed) (plannedData P D H s.nodes s.factor s.seed) (Syntax.planned P D H s)

noncomputable def plannedMachine (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Syntax P D H) :=
  machine (IntegralMixedFramedNormalizationBits.planned P s.nodes s.factor s.seed)
    (planned_access P a s.nodes_native s.factor_native s.seed_native)
    (plannedPlan P D s.nodes s.factor s.seed) (plannedData P D H s.nodes s.factor s.seed) (plannedControls P a D H s)

theorem planned_bounds (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root, 1 ≤ s.factor root)
    (hf : ∀ key, IntegralMixedFramedOriginalBounds.FallbackBounds P D H s.nodes s.seed key) :
    Bounds (IntegralMixedFramedNormalizationBits.planned P s.nodes s.factor s.seed)
      (plannedPlan P D s.nodes s.factor s.seed) (plannedData P D H s.nodes s.factor s.seed) (plannedControls P a D H s) where
  original := planned_familyInputs P D s.nodes s.factor s.seed hs
  factor := hF
  fallback key := (planned_fallback P D H s.nodes s.factor s.seed key).mpr (hf key)
  modulus := planned_budget P s.nodes s.factor s.seed

theorem planned_model_space (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root, 1 ≤ s.factor root)
    (hf : ∀ key, IntegralMixedFramedOriginalBounds.FallbackBounds P D H s.nodes s.seed key) :
    SpaceFunction (plannedMachine P a D H s).model :=
  model_space (IntegralMixedFramedNormalizationBits.planned P s.nodes s.factor s.seed)
    (planned_access P a s.nodes_native s.factor_native s.seed_native)
    (plannedPlan P D s.nodes s.factor s.seed) (plannedData P D H s.nodes s.factor s.seed) (plannedControls P a D H s)
    (planned_bounds P a D H s hs hF hf)

end LeanCanny.Algebra.IntegralMixedFramedNativeBits

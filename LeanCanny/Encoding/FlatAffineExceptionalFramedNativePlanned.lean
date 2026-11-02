/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalFramedNativeControls
public import LeanCanny.Algebra.IntegralMixedFramedNormalizationPlanned
/-! # Automatic arithmetic budgets with the actual initial integer bank

Planning changes only the task encoding and its arithmetic ceilings. The
source-framed instructions and original source queries keep their full saved
keys. Integer leaves are reconstructed from the actual initial bank at the
new encoding, rather than transferred by a coefficient-cost assumption.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalFramedNative
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedHistoryScript (Instruction)
open IntegralMixedFramedNormalizationBits
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width)
open FlatAffineExceptionalFramedIntegerPrelude (plan)
open scoped Classical

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
  all_goals rfl

noncomputable def Body.planned (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Body P D H) :
    Body (IntegralMixedFramedNormalizationBits.planned P s.nodes s.factor s.seed)
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
  nodes := s.nodes
  factor := s.factor
  seed := s.seed
  nodes_native := s.nodes_native
  factor_native := s.factor_native
  seed_native := s.seed_native

noncomputable def plannedControls (P : Parameters) (a : Access P) (base : Plan P)
    {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (input : List Bool → List Bool) (hi : input∈FP)
    (later : (root : List Bool) → List (Instruction (P.ambient root) (P.width root)))
    (hW : ∀ root, width F (input root)≤P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2≤P.cap root+1)
    (hno : ∀ root c, c∈later root → c.command.context≠0)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P (plan P base F C h input later hW hroom))
    (s : Body P (plan P base F C h input later hW hroom) H) :=
  controls (planned P s.nodes s.factor s.seed) (planned_access P a s.nodes_native s.factor_native s.seed_native)
    (plannedPlan P base s.nodes s.factor s.seed) hF C h hh input hi later hW hroom hno
    (plannedData P _ H s.nodes s.factor s.seed) (Body.planned P _ H s)

noncomputable def plannedMachine (P : Parameters) (a : Access P) (base : Plan P)
    {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (input : List Bool → List Bool) (hi : input∈FP)
    (later : (root : List Bool) → List (Instruction (P.ambient root) (P.width root)))
    (hW : ∀ root, width F (input root)≤P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2≤P.cap root+1)
    (hno : ∀ root c, c∈later root → c.command.context≠0)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P (plan P base F C h input later hW hroom))
    (s : Body P (plan P base F C h input later hW hroom) H) :=
  IntegralMixedFramedNativeBits.machine (planned P s.nodes s.factor s.seed)
    (planned_access P a s.nodes_native s.factor_native s.seed_native)
    (plannedPlan P _ s.nodes s.factor s.seed) (plannedData P _ H s.nodes s.factor s.seed)
    (plannedControls P a base hF C h hh input hi later hW hroom hno H s)

theorem planned_bounds (P : Parameters) (a : Access P) (base : Plan P)
    {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (input : List Bool → List Bool) (hi : input∈FP)
    (later : (root : List Bool) → List (Instruction (P.ambient root) (P.width root)))
    (hW : ∀ root, width F (input root)≤P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2≤P.cap root+1)
    (hno : ∀ root c, c∈later root → c.command.context≠0)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P (plan P base F C h input later hW hroom))
    (s : Body P (plan P base F C h input later hW hroom) H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P (plan P base F C h input later hW hroom) s.nodes s.factor s.seed)
    (hfactor : ∀ root, 1≤s.factor root)
    (hf : ∀ key, IntegralMixedFramedOriginalBounds.FallbackBounds P
      (plan P base F C h input later hW hroom) H s.nodes s.seed key) :
    IntegralMixedFramedNativeBits.Bounds (planned P s.nodes s.factor s.seed)
      (plannedPlan P _ s.nodes s.factor s.seed) (plannedData P _ H s.nodes s.factor s.seed)
      (plannedControls P a base hF C h hh input hi later hW hroom hno H s) where
  original := planned_familyInputs P _ s.nodes s.factor s.seed hs
  factor := hfactor
  fallback key := (planned_fallback P _ H s.nodes s.factor s.seed key).mpr (hf key)
  modulus := planned_budget P s.nodes s.factor s.seed

theorem planned_model_space (P : Parameters) (a : Access P) (base : Plan P)
    {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (input : List Bool → List Bool) (hi : input∈FP)
    (later : (root : List Bool) → List (Instruction (P.ambient root) (P.width root)))
    (hW : ∀ root, width F (input root)≤P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2≤P.cap root+1)
    (hno : ∀ root c, c∈later root → c.command.context≠0)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P (plan P base F C h input later hW hroom))
    (s : Body P (plan P base F C h input later hW hroom) H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P (plan P base F C h input later hW hroom) s.nodes s.factor s.seed)
    (hfactor : ∀ root, 1≤s.factor root)
    (hf : ∀ key, IntegralMixedFramedOriginalBounds.FallbackBounds P
      (plan P base F C h input later hW hroom) H s.nodes s.seed key) :
    SpaceFunction (plannedMachine P a base hF C h hh input hi later hW hroom hno H s).model :=
  IntegralMixedFramedNativeBits.model_space _ _ _ _ _
    (planned_bounds P a base hF C h hh input hi later hW hroom hno H s hs hfactor hf)

end LeanCanny.Encoding.FlatAffineExceptionalFramedNative

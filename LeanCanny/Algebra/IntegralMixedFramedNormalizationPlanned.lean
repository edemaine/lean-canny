/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNormalization
/-! # Framed normalization with its derived height and modulus budget

The copied plan keeps the original instructions and source bodies. Native
header representation, original syntax bounds and noncut fallback bounds are
transported explicitly. The planned correctness theorem has no remaining
matrix-height or modulus-budget premise. Its current replies use the new
parameters throughout, without asserting equivalence of old packed queries.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNormalizationBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedStepHeight IntegralMixedFramedOriginalBounds

noncomputable def plannedControls (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : Controls (planned P h.nodes h.factor h.seed) (plannedPlan P D h.nodes h.factor h.seed)
      (plannedData P D H h.nodes h.factor h.seed) where
  tables := h.tables
  native := h.native
  represents := ⟨h.represents.commands,h.represents.fallback⟩
  nodes := h.nodes
  factor := h.factor
  seed := h.seed
  nodes_native := h.nodes_native
  factor_native := h.factor_native
  seed_native := h.seed_native

noncomputable def plannedMachine (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) : Machine :=
  machine (planned P h.nodes h.factor h.seed) (planned_access P a h.nodes_native h.factor_native h.seed_native)
    (plannedPlan P D h.nodes h.factor h.seed) (plannedData P D H h.nodes h.factor h.seed) (plannedControls P D H h)

abbrev PlannedMatches (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) : Prop :=
  Matches (planned P h.nodes h.factor h.seed) (planned_access P a h.nodes_native h.factor_native h.seed_native)
    (plannedPlan P D h.nodes h.factor h.seed) (plannedData P D H h.nodes h.factor h.seed) (plannedControls P D H h) answer

abbrev PlannedRawMatches (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (answer : List Bool → List Bool) : Prop :=
  RawMatches (planned P h.nodes h.factor h.seed) (planned_access P a h.nodes_native h.factor_native h.seed_native)
    (plannedPlan P D h.nodes h.factor h.seed) (plannedData P D H h.nodes h.factor h.seed) (plannedControls P D H h) answer

theorem planned_correct (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) (hs : FamilyInputs P D h.nodes h.factor h.seed) (hF : ∀ root, 1≤h.factor root)
    (hf : ∀ key, FallbackBounds P D H h.nodes h.seed key)
    (x : (q : List Bool) → ZMod (modulus (planned P h.nodes h.factor h.seed) q))
    (hn : PlannedMatches P a D H h (fun q => residueBits (x q)))
    (hr : PlannedRawMatches P a D H h (fun q => residueBits (x q))) :
    Correct (plannedMachine P a D H h) (fun q => residueBits (x q))
      (IntegralMixedRoutineTaskBits.Frame (planned P h.nodes h.factor h.seed)) := by
  apply correct (planned P h.nodes h.factor h.seed) (planned_access P a h.nodes_native h.factor_native h.seed_native)
    (plannedPlan P D h.nodes h.factor h.seed) (plannedData P D H h.nodes h.factor h.seed) (plannedControls P D H h)
    (planned_familyInputs P D h.nodes h.factor h.seed hs) hF _ (planned_budget P h.nodes h.factor h.seed) x hn hr
  intro key
  exact (planned_fallback P D H h.nodes h.factor h.seed key).mpr (hf key)

theorem planned_canonical (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) :
    ∃ z : ZMod (modulus (planned P h.nodes h.factor h.seed) q), residueBits z=(plannedMachine P a D H h).model q :=
  canonical (planned P h.nodes h.factor h.seed) (planned_access P a h.nodes_native h.factor_native h.seed_native)
    (plannedPlan P D h.nodes h.factor h.seed) (plannedData P D H h.nodes h.factor h.seed) (plannedControls P D H h) q

theorem planned_producer_matches (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (answer : List Bool → List Bool) (hn : PlannedMatches P a D H h answer) :
    IntegralMixedNormalizedCompanionBits.ScopedNormalizationMatches (planned P h.nodes h.factor h.seed)
      (IntegralMixedFramedHistoryFamilyBits.family (planned P h.nodes h.factor h.seed)
        (plannedPlan P D h.nodes h.factor h.seed) (plannedData P D H h.nodes h.factor h.seed)) answer :=
  producer_matches (planned P h.nodes h.factor h.seed) (planned_access P a h.nodes_native h.factor_native h.seed_native)
    (plannedPlan P D h.nodes h.factor h.seed) (plannedData P D H h.nodes h.factor h.seed) (plannedControls P D H h) answer hn

end LeanCanny.Algebra.IntegralMixedFramedNormalizationBits

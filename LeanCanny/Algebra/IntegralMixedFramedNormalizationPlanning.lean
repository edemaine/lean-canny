/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRawHeightControls
public import LeanCanny.Algebra.IntegralMixedNormalizationHeight
/-! # Cycle-free height and modulus planning for framed normalization

The top-matrix ceiling and characteristic budget ignore both fields being
planned. Enlarging the modulus budget also preserves the original budget.
This chooses a new task encoding; it does not identify old and new packed
query words or route across different original roots.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNormalizationBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedRawHeight IntegralMixedFramedStepHeight IntegralMixedNormalizationTopBits
open IntegralMixedFramedHistoryFamilyBits (Plan)

theorem rootCeiling_update_modulusBound (P : Parameters) (L F C : List Bool → ℕ)
    (newModulus : List Bool → ℕ) (root : List Bool) :
    rootCeiling {P with modulusBound:=newModulus} L F C root=rootCeiling P L F C root := rfl

def requiredModulus (P : Parameters) (L F C : List Bool → ℕ) (root : List Bool) : ℕ :=
  2*characteristicBudget P (rootCeiling P L F C) root+4

theorem requiredModulus_binary (P : Parameters) (a : Access P) {L F C : List Bool → ℕ}
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : BinaryFn (requiredModulus P L F C) :=
  ((BinaryFn.const 2).mul (characteristicBudget_binary P a _ (rootCeiling_binary P a hL hF hC))).add (BinaryFn.const 4)

def planned (P : Parameters) (L F C : List Bool → ℕ) : Parameters :=
  { P with height:=rootCeiling P L F C
           modulusBound:=fun root => max (P.modulusBound root) (requiredModulus P L F C root) }

theorem planned_access (P : Parameters) (a : Access P) {L F C : List Bool → ℕ}
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : Access (planned P L F C) where
  cap := a.cap
  width := a.width
  ambient := a.ambient
  sourceWidth := a.sourceWidth
  degree := a.degree
  height := rootCeiling_binary P a hL hF hC
  modulusBound := by
    change BinaryFn (fun root => max (P.modulusBound root) (requiredModulus P L F C root))
    simpa only [max_def] using BinaryFn.ite (a.modulusBound.le (requiredModulus_binary P a hL hF hC))
      (requiredModulus_binary P a hL hF hC) a.modulusBound

theorem planned_ceiling (P : Parameters) (L F C : List Bool → ℕ) (root : List Bool) :
    rootCeiling (planned P L F C) L F C root=rootCeiling P L F C root := rfl

theorem planned_requiredModulus (P : Parameters) (L F C : List Bool → ℕ) (root : List Bool) :
    requiredModulus (planned P L F C) L F C root=requiredModulus P L F C root := rfl

theorem planned_budget (P : Parameters) (L F C : List Bool → ℕ) (root : List Bool) :
    2*characteristicBudget (planned P L F C) (rootCeiling (planned P L F C) L F C) root+4≤
      (planned P L F C).modulusBound root := le_max_right _ _

theorem planned_preserves_modulus (P : Parameters) (L F C : List Bool → ℕ) (root : List Bool) :
    P.modulusBound root≤(planned P L F C).modulusBound root := le_max_left _ _

def plannedPlan (P : Parameters) (D : Plan P) (L F C : List Bool → ℕ) : Plan (planned P L F C) where
  initialSource := D.initialSource
  initial_degree := D.initial_degree
  scalar_cap := D.scalar_cap
  rules := D.rules
  room := D.room

noncomputable def plannedData (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ) :
    IntegralMixedFramedHistoryFamilyBits.Data (planned P L F C) (plannedPlan P D L F C) where
  degree_eq := H.degree_eq
  sourceWidth := H.sourceWidth
  fallback := H.fallback

theorem planned_familyInputs (P : Parameters) (D : Plan P) (L F C : List Bool → ℕ)
    (h : FamilyInputs P D L F C) : FamilyInputs (planned P L F C) (plannedPlan P D L F C) L F C where
  script := h.script
  default := h.default

theorem planned_instruction (P : Parameters) (D : Plan P) (L F C : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.instruction (planned P L F C) (plannedPlan P D L F C) key=
      IntegralMixedFramedHistoryFamilyBits.instruction P D key := rfl

theorem planned_fallback (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedOriginalBounds.FallbackBounds (planned P L F C) (plannedPlan P D L F C)
      (plannedData P D H L F C) L C key ↔ IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key := by
  cases hc : (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;>
    simp only [IntegralMixedFramedOriginalBounds.FallbackBounds,planned_instruction,plannedData,hc] <;> rfl

end LeanCanny.Algebra.IntegralMixedFramedNormalizationBits

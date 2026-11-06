/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryNativeGraph
public import LeanCanny.Connectivity.CanonicalWholeDecision
/-! # Original whole-space connectivity from the constructive native frontier -/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryNativeDecision
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (D:SpaceDecider FormulaSignSlotRadialGuardedFeasibility.language)
include D in
theorem connected_mem_PSPACE:connectedLanguage∈PSPACE:=by
  have HC:=(CanonicalAuxiliaryNativeGraph.connected_computable D).comp
    (.of_polyTime Input.wholeFrame_mem_FP)
  have HP:=ComputableTidilyInPolySpace.of_polyTime Input.isWhole_fppred.computable
  have HW:=ComputableTidilyInPolySpace.of_polyTime CanonicalEndpointNative.wellFormed_computable
  have HF:ComputableTidilyInPolySpace (fun _:List Bool=>false) encBits encBool:=.of_polyTime (.const false)
  apply NativeSpace.of_computable (HP.ite (HW.ite HC HF) HF)
  intro c
  by_cases hp:Input.IsWhole c
  · obtain ⟨d,rfl⟩:=(Input.isWhole_iff c).mp hp
    simp only [hp,decide_true,ite_true,CanonicalEndpointNative.description_whole,decide_eq_true_eq]
    by_cases hd:d.WellFormed
    · simp only [hd,ite_true,decide_eq_true_eq,CanonicalEndpointNative.wholeFrame_whole]
      exact (CanonicalAuxiliaryNativeGraph.connected_iff d hd).symm
    · have HB:(Input.whole d).encode∉connectedLanguage:=by
        rw [whole_encode_mem_iff]
        exact fun h=>hd h.1
      simp only [hd,ite_false,Bool.false_eq_true]
      exact iff_of_false HB id
  · have HB:c∉connectedLanguage:=by
      rintro ⟨d,rfl,_⟩
      exact hp ((Input.isWhole_iff _).mpr ⟨d,rfl⟩)
    simp only [hp,decide_false,ite_false,Bool.false_eq_true]
    exact iff_of_false HB id
end LeanCanny.Connectivity.CanonicalAuxiliaryNativeDecision

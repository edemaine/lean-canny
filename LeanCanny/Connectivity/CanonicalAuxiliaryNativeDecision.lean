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
  apply CanonicalEndpointNative.connected_mem_PSPACE_of_test HC
  intro d hd
  simpa only [Function.comp_apply, CanonicalEndpointNative.wholeFrame_whole, decide_eq_true_eq]
    using (CanonicalAuxiliaryNativeGraph.connected_iff d hd).symm

end LeanCanny.Connectivity.CanonicalAuxiliaryNativeDecision

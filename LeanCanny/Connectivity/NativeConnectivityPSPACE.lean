/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryNativeDecision
public import LeanCanny.Connectivity.CanonicalAuxiliaryNativePointSearch
public import LeanCanny.Connectivity.FormulaSignSlotRadialGuardedFeasibilityNative
/-! # Native PSPACE membership for the original connectivity languages

The input includes the dimension and arbitrary Boolean polynomial formulas.
All geometric witness tests are implemented by the same-word native decider.
-/
@[expose] public section
namespace LeanCanny.Connectivity
open LeanCanny.Computation

/-- The original whole-space language, including empty spaces and rejection of
malformed inputs, is in native PSPACE without a computational premise. -/
theorem connectedLanguage_mem_PSPACE : connectedLanguage ∈ PSPACE :=
  CanonicalAuxiliaryNativeDecision.connected_mem_PSPACE FormulaSignSlotRadialGuardedFeasibilityNative.decider


/-- The original point language uses singleton endpoint formulas and rejects
malformed, ill-scoped, inconsistent and nonunique endpoint descriptions. -/
theorem pointLanguage_mem_PSPACE : pointLanguage ∈ PSPACE :=
  CanonicalAuxiliaryNativePointSearch.point_mem_PSPACE FormulaSignSlotRadialGuardedFeasibilityNative.decider

end LeanCanny.Connectivity

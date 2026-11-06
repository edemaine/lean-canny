/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderTerminalFiber
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphPointGlue
/-! # The actual provider depth-completeness predicate and its terminal case -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider" => FormulaSignSlotRadialProviderAtomic.provider
local notation "depth" => FormulaSignSlotRadialProviderAtomic.depth
local notation "num" => FormulaSignSlotRadialProviderMarkedGeometry.number

noncomputable def DepthComplete (c : List Bool) (k : ℕ) : Prop :=
  ∀a b,∀ha : A a,∀hb : A b,∀hca : provider a=c,∀hcb : provider b=c,
    depth a=k→depth b=k→
      JoinedIn (frozenSlice c k (FormulaSignSlotRadialProviderAtomic.levels a ha))
        (pointAt c a ha hca) (pointAt c b hb hcb)→RawReachable c a b

theorem depth_complete_terminal (c : List Bool) : DepthComplete c (num c+3) := by
  intro a b ha hb hca hcb hta _ HP
  exact (terminal_fiber_glue c a b ha hb hca hcb hta HP).2

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph

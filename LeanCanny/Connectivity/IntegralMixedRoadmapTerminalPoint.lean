/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapTerminalFiber
/-! # Terminal fiber paths identify an arbitrary geometric target

The target need not already have a native history. This lets a terminal
accepted history itself become the marker for its prescribed prelude point.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR Set
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.levels pointAt
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)

theorem terminal_pointAt_eq_of_joined (candidate old :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hc :IntegralMixedRoadmapAtomic.candidate old=candidate)
    (hd :IntegralMixedRoadmapAtomic.depth old=n (pairFst candidate)+3)
    (target :Fin (n (pairFst candidate)+3+1)→ℝ)
    (HJ :JoinedIn (frozenSlice (n:=n) (t:=t) (R0:=R0) candidate (n (pairFst candidate)+3)
      (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 old hv))
      (pointAt hn ht ha hR0 candidate old hv hc) target):
    pointAt hn ht ha hR0 candidate old hv hc=target:=by
  let fiber:=frozenSlice (n:=n) (t:=t) (R0:=R0) candidate (n (pairFst candidate)+3)
    (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 old hv)
  have HF:=terminal_frozenSlice_finite hn ht ha hR0 candidate old hv hc hd
  let :Finite fiber:=HF.to_subtype
  let :TotallyDisconnectedSpace fiber:=inferInstance
  have HE :(⟨pointAt hn ht ha hR0 candidate old hv hc,HJ.source_mem⟩ :fiber)=
      ⟨target,HJ.target_mem⟩:=
    isPreconnected_connectedComponent.subsingleton mem_connectedComponent
      (pathComponent_subset_component _ HJ.joined_subtype)
  exact congrArg Subtype.val HE

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapRetainedTargetChild
public import LeanCanny.Connectivity.IntegralMixedRoadmapMarkedPointAt
public import LeanCanny.Connectivity.IntegralMixedRoadmapTerminalPoint
public import LeanCanny.Connectivity.IntegralMixedRoadmapAnchorIncidence
/-! # Native attachment to the prelude target by remaining-coordinate induction -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Connectivity LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.depth
  IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapAtomic.levels
  IntegralMixedRoadmapRetainedAppend.ownPoint IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedRoadmapRetainedAppend.parentState IntegralMixedRoadmapRetainedAppend.parentValues
  canonicalPointAt pointAt preludeAt

noncomputable def PreludeTargetComplete (candidate :List Bool) (k :ℕ):Prop:=
  ∀old,∀(hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old),
    ∀(hc :IntegralMixedRoadmapAtomic.candidate old=candidate),
    IntegralMixedRoadmapAtomic.depth old=k→
    ∀target :Fin (n (pairFst candidate)+3+1)→ℝ,
    preludeAt hn ht ha hR0 candidate old hv hc=target→
    JoinedIn (frozenSlice (n:=n) (t:=t) (R0:=R0) candidate (IntegralMixedRoadmapAtomic.depth old)
      (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 old hv))
      (pointAt hn ht ha hR0 candidate old hv hc) target→
    ∃finished,∃(hFinished :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 finished),
      ∃(hcFinished :IntegralMixedRoadmapAtomic.candidate finished=candidate),
      IntegralMixedRoadmapAtomic.depth finished=n (pairFst candidate)+3 ∧
      RawReachable hn ht ha hR0 candidate old finished ∧
      pointAt hn ht ha hR0 candidate finished hFinished hcFinished=target ∧
      preludeAt hn ht ha hR0 candidate finished hFinished hcFinished=target

theorem prelude_target_complete_terminal (candidate :List Bool):
    PreludeTargetComplete hn ht ha hR0 candidate (n (pairFst candidate)+3):=by
  intro old hv hc hDepth target HPrelude HPath
  have HE:=terminal_pointAt_eq_of_joined hn ht ha hR0 candidate old hv hc hDepth target
    (by simpa only [hDepth] using HPath)
  exact ⟨old,hv,hc,hDepth,⟨hv,hv,hc,hc,Relation.ReflTransGen.refl⟩,HE,HPrelude⟩

theorem prelude_target_complete_step (candidate :List Bool) (k :ℕ)
    (hk :k<n (pairFst candidate)+3)
    (IH :PreludeTargetComplete hn ht ha hR0 candidate (k+1)):
    PreludeTargetComplete hn ht ha hR0 candidate k:=by
  intro old hv hc hDepth target HPrelude HPath
  subst candidate
  have hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old:=by
    rw [hDepth,IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0 old]
    exact hk
  let p:=IntegralMixedRoadmapRetainedAppend.ownPoint hn ht ha hR0 old hv
  have HPointP :canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl p=
      pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old hv rfl:=
    canonicalPointAt_ownPoint hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old hv rfl
  have HImage:=canonical_slice_image hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old hv hd rfl
  have HTarget:=HPath.target_mem
  rw [←HImage] at HTarget
  obtain ⟨q,HQ,HPointQ⟩:=HTarget
  have HCanonical:=(canonical_slice_joined_iff hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
    old hv hd rfl p q).mpr (by simpa only [HPointP,HPointQ] using HPath)
  obtain ⟨targetRef,HRef⟩:=prelude_target_reference hn ht ha hR0 old hv hd q (HPointQ.trans HPrelude.symm)
  obtain ⟨child,hChild,hcChild,hDepthChild,HRaw,HFields,HChildPath⟩:=
    exists_child_toward_target hn ht ha hR0 old hv hd targetRef q HRef HCanonical
  have HValues (idx :ℕ) (hi :idx≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old):
      IntegralMixedRoadmapMarkedPrelude.value hn ht ha hR0 old hv idx=
        IntegralMixedRoadmapMarkedPrelude.value hn ht ha hR0 child hChild idx:=by
    have HF:=HFields idx (IntegralMixedRoadmapMarkedPrelude.coordinate_before_parent hn ht ha hR0 old idx hi)
    change IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 old hv idx=
      IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 child hChild idx
    exact HF.symm
  have HPreludeEqual:=preludeAt_eq_of_fields hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
    old child hv hChild rfl hcChild HValues
  have HPreludeChild:=HPreludeEqual.symm.trans HPrelude
  have HChildTarget :JoinedIn (frozenSlice (n:=n) (t:=t) (R0:=R0) (IntegralMixedRoadmapAtomic.candidate old)
      (IntegralMixedRoadmapAtomic.depth child) (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 child hChild))
      (pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) child hChild hcChild) target:=by
    simpa only [HPointQ] using HChildPath
  obtain ⟨finished,hFinished,hcFinished,hDepthFinished,HReach,HPoint,HPreludeFinished⟩:=
    IH child hChild hcChild (by omega) target HPreludeChild HChildTarget
  exact ⟨finished,hFinished,hcFinished,hDepthFinished,raw_reachable_trans hn ht ha hR0 HRaw HReach,
    HPoint,HPreludeFinished⟩

/-- No recursive attachment premise remains: retained prelude coordinates
supply every new target height, including noncritical boundary heights. -/
theorem prelude_target_complete (candidate :List Bool) (k :ℕ) (hk :k≤n (pairFst candidate)+3):
    PreludeTargetComplete hn ht ha hR0 candidate k:=by
  induction hk using Nat.decreasingInduction with
  | self => exact prelude_target_complete_terminal hn ht ha hR0 candidate
  | of_succ k hk ih => exact prelude_target_complete_step hn ht ha hR0 candidate k hk ih

/-- A genuine frozen-slice path to the bound prelude constructs an actual
reachable terminal MarkerAt word, without assuming a marker in advance. -/
theorem incidence_of_prelude_path (candidate old :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hc :IntegralMixedRoadmapAtomic.candidate old=candidate)
    (hr :IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 old)
    (HPath :JoinedIn (frozenSlice (n:=n) (t:=t) (R0:=R0) candidate (IntegralMixedRoadmapAtomic.depth old)
      (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 old hv))
      (pointAt hn ht ha hR0 candidate old hv hc) (preludeAt hn ht ha hR0 candidate old hv hc)):
    IntegralMixedRoadmapAnchorIncidence.Incidence hn ht ha hR0 candidate old:=by
  have HBound :IntegralMixedRoadmapAtomic.depth old≤n (pairFst candidate)+3:=by
    have H:=IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 old hv
    rw [IntegralMixedRoadmapAtomic.dimension_eq] at H
    exact H.trans_eq (congrArg (fun c=>n (pairFst c)+3) hc)
  obtain ⟨finished,hFinished,hcFinished,hDepth,HRaw,HPoint,HPrelude⟩:=
    prelude_target_complete hn ht ha hR0 candidate (IntegralMixedRoadmapAtomic.depth old) HBound
      old hv hc rfl (preludeAt hn ht ha hR0 candidate old hv hc) rfl HPath
  have HReplay:=replay_of_preludeAt_eq hn ht ha hR0 candidate old finished hv hFinished hc hcFinished hr HPrelude.symm
  have HDim :IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 finished=n (pairFst candidate)+3:=by
    rw [IntegralMixedRoadmapAtomic.dimension_eq]
    exact congrArg (fun c=>n (pairFst c)+3) hcFinished
  have HMarker :finished∈IntegralMixedRoadmapMarkerAt.language hn ht ha hR0:=
    (markerAt_iff hn ht ha hR0 candidate finished hFinished hcFinished).mpr
      ⟨hDepth.trans HDim.symm,HReplay,HPoint.trans HPrelude.symm⟩
  exact ⟨finished,HMarker,HRaw⟩

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

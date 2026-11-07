/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderRetainedTargetChild
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderPreludeTargetGeometry
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderMarkedAnchor
/-! # Actual reachable attachment to the same word's retained marked prelude -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity
open FormulaSignSlotRadialProviderGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A"=>FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider"=>FormulaSignSlotRadialProviderAtomic.provider
local notation "depth"=>FormulaSignSlotRadialProviderAtomic.depth
local notation "dim"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "initial"=>FormulaSignSlotRadialProviderAtomic.initial
local notation "field"=>FormulaSignSlotRadialProviderAtomic.field
local notation "num"=>FormulaSignSlotRadialProviderMarkedGeometry.number
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.depth
  FormulaSignSlotRadialProviderAtomic.point FormulaSignSlotRadialProviderAtomic.levels
  FormulaSignSlotRadialProviderAtomic.field FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderRetainedAppend.ownPoint FormulaSignSlotRadialProviderRetainedAppend.preparedRoot
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentValues
  providerPoint pointAt preludeAt

noncomputable def PreludeTargetComplete (c :List Bool) (k :ℕ):Prop:=
  ∀old,∀hv:A old,∀hc:provider old=c,depth old=k→∀target:Fin (num c+4)→ℝ,
    preludeAt c old hv hc=target→
    JoinedIn (frozenSlice c (depth old) (FormulaSignSlotRadialProviderAtomic.levels old hv))
      (pointAt c old hv hc) target→
    ∃finished,∃hFinished:A finished,∃hcFinished:provider finished=c,
      depth finished=num c+3 ∧RawReachable c old finished ∧
      pointAt c finished hFinished hcFinished=target ∧preludeAt c finished hFinished hcFinished=target ∧
      ∀i < initial old,field finished hFinished i=field old hv i

theorem prelude_target_complete_terminal (c :List Bool):PreludeTargetComplete c (num c+3):=by
  intro old hv hc hDepth target HPrelude HPath
  have HE:=terminal_pointAt_eq_of_joined c old hv hc hDepth target (by simpa only [hDepth] using HPath)
  exact ⟨old,hv,hc,hDepth,raw_reachable_refl c old hv hc,HE,HPrelude,fun _ _=>rfl⟩

theorem prelude_target_complete_step (c :List Bool) (k :ℕ) (hk:k<num c+3)
    (IH:PreludeTargetComplete c (k+1)):PreludeTargetComplete c k:=by
  intro old hv hc hDepth target HPrelude HPath
  subst c
  have HDim:dim old=num (provider old)+3:=FormulaSignSlotRadialProviderAtomic.dimension_provider old
  have hd:depth old<dim old:=by omega
  let p:=FormulaSignSlotRadialProviderRetainedAppend.ownPoint old hv
  have HPointP:providerPoint old p=pointAt (provider old) old hv rfl:=
    eq_of_heq ((providerPoint_heq old p).trans
      ((FormulaSignSlotRadialProviderRetainedAppend.ownPoint_heq old hv).trans (native_pointAt_heq _ old hv rfl)))
  have HTarget:=HPath.target_mem
  rw [←providerPoint_slice_image old hv hd] at HTarget
  obtain ⟨q,HQ,HPointQ⟩:=HTarget
  have HCanonical:=(providerPoint_joined_iff old hv hd p q).mp
    (by simpa only [HPointP,HPointQ] using HPath)
  obtain ⟨targetRef,HRef⟩:=prelude_target_reference old hv hd q (HPointQ.trans HPrelude.symm)
  obtain ⟨child,hChild,hcChild,hDepthChild,HRaw,HFields,HChildPath⟩:=
    exists_child_toward_target old hv hd targetRef q HRef HCanonical
  have HInitial:∀i < initial old,field child hChild i=field old hv i:=
    fun i hi=>HFields i (hi.trans_le (initial_le_begin old))
  have HPreludeEqual:=preludeAt_eq_of_fields (provider old) old child hv hChild rfl hcChild
    (fun i hi=>(HInitial i hi).symm)
  have HPreludeChild:=HPreludeEqual.symm.trans HPrelude
  have HChildTarget:JoinedIn (frozenSlice (provider old) (depth child)
      (FormulaSignSlotRadialProviderAtomic.levels child hChild)) (pointAt (provider old) child hChild hcChild) target:=by
    simpa only [HPointQ] using HChildPath
  obtain ⟨finished,hFinished,hcFinished,hDepthFinished,HReach,HPoint,HPreludeFinished,HFinalFields⟩:=
    IH child hChild hcChild (by omega) target HPreludeChild HChildTarget
  refine ⟨finished,hFinished,hcFinished,hDepthFinished,raw_reachable_trans HRaw HReach,HPoint,HPreludeFinished,?_⟩
  have HCount:initial child=initial old:=by
    rw [FormulaSignSlotRadialProviderAtomic.initial_provider,FormulaSignSlotRadialProviderAtomic.initial_provider,hcChild]
  intro i hi
  exact (HFinalFields i (hi.trans_eq HCount.symm)).trans (HInitial i hi)

theorem prelude_target_complete (c :List Bool) (k :ℕ) (hk:k≤num c+3):PreludeTargetComplete c k:=by
  induction hk using Nat.decreasingInduction with
  | self => exact prelude_target_complete_terminal c
  | of_succ k hk ih => exact prelude_target_complete_step c k hk ih

/-- A genuine path to the word's own prelude constructs a native reachable
terminal marked anchor, retaining every original initial field. -/
theorem exists_reachable_marked_anchor (c old :List Bool) (hv:A old) (hc:provider old=c)
    (HPath:JoinedIn (frozenSlice c (depth old) (FormulaSignSlotRadialProviderAtomic.levels old hv))
      (pointAt c old hv hc) (preludeAt c old hv hc)):
    ∃finished,∃hFinished:A finished,∃_hcFinished:provider finished=c,
      depth finished=num c+3 ∧RawReachable c old finished ∧
      finished∈FormulaSignSlotRadialProviderMarkedAnchor.language ∧
      ∀i < initial old,field finished hFinished i=field old hv i:=by
  have HDim0:dim old=num (provider old)+3:=FormulaSignSlotRadialProviderAtomic.dimension_provider old
  have HDim:dim old=num c+3:=by simpa only [hc] using HDim0
  have HBound:depth old≤num c+3:=
    (FormulaSignSlotRadialProviderAtomic.depth_le old (FormulaSignSlotRadialProviderAtomic.valid_grammar old hv)).trans_eq HDim
  obtain ⟨finished,hFinished,hcFinished,hDepth,HRaw,HPoint,HPrelude,HFields⟩:=
    prelude_target_complete c (depth old) HBound old hv hc rfl (preludeAt c old hv hc) rfl HPath
  have HNative:HEq (FormulaSignSlotRadialProviderAtomic.point finished hFinished)
      (FormulaSignSlotRadialProviderAtomic.MarkedPrelude.preludePoint finished hFinished):=
    (native_pointAt_heq c finished hFinished hcFinished).trans
      ((heq_of_eq (HPoint.trans HPrelude.symm)).trans (preludeAt_heq c finished hFinished hcFinished).symm)
  exact ⟨finished,hFinished,hcFinished,hDepth,HRaw,
    (FormulaSignSlotRadialProviderMarkedAnchor.language_native_iff finished hFinished).mpr HNative,HFields⟩

/-- At depth zero the only path premise is in the actual common spatial zero set. -/
theorem exists_reachable_marked_anchor_of_source_path (c old :List Bool) (hv:A old) (hc:provider old=c)
    (h0:depth old=0)
    (HPath:JoinedIn (FormulaSignSlotRadialProviderMarkedGeometry.zeroSet c)
      (pointAt c old hv hc) (preludeAt c old hv hc)):
    ∃finished,∃hFinished:A finished,∃_hcFinished:provider finished=c,
      depth finished=num c+3 ∧RawReachable c old finished ∧
      finished∈FormulaSignSlotRadialProviderMarkedAnchor.language ∧
      ∀i < initial old,field finished hFinished i=field old hv i:=by
  have HZero:frozenSlice c (depth old) (FormulaSignSlotRadialProviderAtomic.levels old hv)=
      FormulaSignSlotRadialProviderMarkedGeometry.zeroSet c:=by
    ext p
    constructor
    · exact fun hp=>hp.1
    · intro hp
      exact ⟨hp,fun i hi=>False.elim (by omega)⟩
  exact exists_reachable_marked_anchor c old hv hc (by simpa only [HZero] using HPath)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend

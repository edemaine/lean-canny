/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphCanonicalPoints
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphChildFiber
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicMarkedPrelude
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPlan
/-! # Own initial prelude coordinates are actual retained canonical targets -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open IntegralMixedHistory IntegralMixedFrozenFrame
open FormulaSignSlotRadialProviderRetainedAppend (preparedRoot parentDescriptor parentValues)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A"=>FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider"=>FormulaSignSlotRadialProviderAtomic.provider
local notation "depth"=>FormulaSignSlotRadialProviderAtomic.depth
local notation "dim"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "num"=>FormulaSignSlotRadialProviderMarkedGeometry.number
local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "E"=>FormulaSignSlotRadialProviderAtomic.ownBirth
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderAtomic.field FormulaSignSlotRadialProviderRetainedAppend.preparedRoot
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor FormulaSignSlotRadialProviderRetainedAppend.parentValues
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands

noncomputable def preludeAt (c q :List Bool) (hv :A q) (_hc :provider q=c) :Fin (num c+4)→ℝ:=
  fun i=>FormulaSignSlotRadialProviderAtomic.field q hv i.val

theorem preludeAt_heq (c q :List Bool) (hv :A q) (hc :provider q=c) :
    HEq (FormulaSignSlotRadialProviderAtomic.MarkedPrelude.preludePoint q hv) (preludeAt c q hv hc):=by
  subst c
  rfl

theorem initial_le_begin (old :List Bool) :FormulaSignSlotRadialProviderAtomic.initial old≤
    FormulaSignSlotRadialProviderProperAppend.beginBirth old:=by
  rw [FormulaSignSlotRadialProviderProperAppend.begin_eq_start]
  omega

theorem preludeAt_eq_of_fields (c old child :List Bool) (hv :A old) (hw :A child)
    (hc :provider old=c) (hd :provider child=c)
    (HF :∀i<FormulaSignSlotRadialProviderAtomic.initial old,
      FormulaSignSlotRadialProviderAtomic.field old hv i=FormulaSignSlotRadialProviderAtomic.field child hw i) :
    preludeAt c old hv hc=preludeAt c child hw hd:=by
  funext i
  have HD0:dim old=num (provider old)+3:=FormulaSignSlotRadialProviderAtomic.dimension_provider old
  have HD:dim old=num c+3:=by simpa only [hc] using HD0
  have HI:=FormulaSignSlotRadialProviderAtomic.initial_eq old
  exact HF i.val (by have HB:=i.isLt;omega)

variable (old :List Bool) (hv :A old) (hd :depth old<dim old)
local notation "he"=>FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "r"=>preparedRoot old (E old)
local notation "cs"=>FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd (E old) he
local notation "d"=>parentDescriptor old hv hd (E old) he
local notation "V"=>parentValues old hv hd (E old) he
local notation "hk"=>FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd (E old) he
local notation "h"=>IntegralMixedChronologicalSweepFrame.next d hk

theorem prelude_target_reference (q :Fin ((P).ambient r+1)→ℝ)
    (HQ :providerPoint old q=preludeAt (provider old) old hv rfl):
    ∃targetRef:Fin (cs).length,q h=V targetRef:=by
  have HL:=FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd (E old) he
  have HB:=(FormulaSignSlotRadialProviderRetainedAppend.parent_length old hv hd (E old) he).trans
    (FormulaSignSlotRadialProviderRetainedAppend.begin_eq old)
  have HN:=FormulaSignSlotRadialProviderAtomic.initial_eq old
  have HFit:depth old<(cs).length:=by omega
  let targetRef:Fin (cs).length:=⟨(cs).length-1-depth old,by omega⟩
  have HV:V targetRef=FormulaSignSlotRadialProviderAtomic.field old hv (depth old):=by
    rw [FormulaSignSlotRadialProviderRetainedAppend.parent_values]
    apply congrArg (FormulaSignSlotRadialProviderAtomic.field old hv)
    dsimp only [targetRef]
    omega
  let coord:=childCoordinate (provider old) old hv rfl
  have HCoord:Fin.cast (parent_point_dimension old).symm coord=h:=by
    apply Fin.ext
    simp only [Fin.val_cast,coord,childCoordinate_val,IntegralMixedChronologicalSweepFrame.next]
    exact HL.symm
  have HH:=congrFun HQ coord
  change q (Fin.cast (parent_point_dimension old).symm coord)=
    FormulaSignSlotRadialProviderAtomic.field old hv coord.val at HH
  rw [HCoord] at HH
  exact ⟨targetRef,HH.trans HV.symm⟩

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph

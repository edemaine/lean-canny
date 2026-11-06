/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendColumns
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendSampledLevel
/-! # The own sampled tuple retains every local MID and child powered coordinate -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalEndpoint
open IntegralMixedFramedPhysicalIndex (arity enumerate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem local_column_lt (a span blocks off i :ℕ) (h :off<blocks) (hi :i<span) :
    a+span*off+i<a+span*blocks:=by
  have HM:=Nat.mul_le_mul_left span (show off+1≤blocks by omega)
  have HI:a+span*off+i<a+span*(off+1):=by rw [Nat.mul_succ];omega
  exact HI.trans_le (Nat.add_le_add_left HM a)

local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
variable (old :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd :FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
local notation "e"=>FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he"=>FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c"=>FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e
local notation "cs"=>FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "hk"=>FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he
local notation "g"=>FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he
local notation "hg"=>FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd e he
local notation "hQ"=>IntegralMixedStaticRecordPrefix.cap (FormulaSignSlotRadialProviderRecordPlan.spatial c)
  (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap c)
variable (left right :ParentEndpoint old hv hd) (R :CanonicalPair old hv hd left right) (side :Bool)
local notation "Dold"=>FormulaSignSlotRadialProviderAtomic.dimension old
local notation "Kold"=>Dold-FormulaSignSlotRadialProviderAtomic.depth old
local notation "mid"=>midpointBirth old hv hd left right R
local notation "finish"=>finishBirth old hv hd left right R side
local notation "base"=>endpointArity old hv hd left right R
local notation "C"=>canonicalObservation old hv hd left right R side
noncomputable local instance providerProperPoweredReadbackFintype :Fintype (Index (Fin 0) cs):=
  indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot preparedRoot
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.depth

private theorem powered_midpoint_clock :(cs).length+R.result.commands.length=mid:=by
  have HP:=FormulaSignSlotRadialProviderRetainedAppend.parent_length old hv hd e he
  change (cs).length=beginBirth old at HP
  unfold midpointBirth
  omega

private theorem powered_free_count :(R.orderedFree hk).length=Kold:=by
  have HQ:(R.orderedFree hk).length=(P).ambient c+1-
      ((FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd e he).labels.length+1):=
    R.orderedFree_length hk
  have HD:(P).ambient c=Dold:=FormulaSignSlotRadialProviderRetainedAppend.prepared_dimension old e
  have HL:=FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd e he
  omega

private theorem powered_span :2*(P).ambient c+4=2*Dold+4:=
  congrArg (fun n=>2*n+4) (FormulaSignSlotRadialProviderRetainedAppend.prepared_dimension old e)

include side in
theorem canonical_local_arity :(C).arity=base+(2*Dold+4)*(2+2*Kold):=by
  have HA:=R.level_physical_arity hQ cs hk g hg side
  change (C).arity=base+(2*(P).ambient c+4)*(2+2*(R.orderedFree hk).length) at HA
  rw [powered_span old,powered_free_count old hv hd left right R] at HA
  exact HA

theorem SampledLevel.local_powered
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (S :SampledLevel old hv hd left right R side pMID pChild)
    (b :ℕ) (hb0 :mid≤b) (hb1 :b<finish) (j :Fin ((P).ambient c+1)) :
    S.receipt.tuple (base+(2*Dold+4)*(b-mid)+j.val)^
      UniformIntegralPowerSchedule.physical ((P).cap c+1) (2^(P).width c) b=
      if b<mid+1+Kold then pMID j else pChild j:=by
  have HM:=powered_midpoint_clock old hv hd left right R
  have HK:=powered_free_count old hv hd left right R
  have HF:=finish_eq old hv hd left right R side
  have HB0:(cs).length+R.result.commands.length≤b:=by omega
  have HB1:b<(cs).length+R.result.commands.length+2+2*(R.orderedFree hk).length:=by omega
  obtain ⟨A,E,ordinal,HE,N⟩:=S.physical
  have HN:=NativePair.NaturalReadback.powered_block hQ cs R hk g hg _ _ _ side _
    pMID pChild A E N HE b HB0 HB1 j
  change S.localTuple (base+(2*(P).ambient c+4)*(b-((cs).length+R.result.commands.length))+j.val)^
      UniformIntegralPowerSchedule.physical ((P).cap c+1) (2^(P).width c) b=
      if b<(cs).length+R.result.commands.length+1+(R.orderedFree hk).length then pMID j else pChild j at HN
  rw [HM,HK,powered_span old] at HN
  have HJ:j.val<2*Dold+4:=by
    have HD:=FormulaSignSlotRadialProviderRetainedAppend.prepared_dimension old e
    have HI:=j.isLt
    omega
  have HR:b-mid<2+2*Kold:=by omega
  have HC:base+(2*Dold+4)*(b-mid)+j.val<(C).arity:=
    (local_column_lt base (2*Dold+4) (2+2*Kold) (b-mid) j.val HR HJ).trans_eq
      (canonical_local_arity old hv hd left right R side).symm
  rw [S.receipt.preserved _ HC]
  exact HN

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend

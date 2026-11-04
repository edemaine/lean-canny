/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendChild
public import LeanCanny.Algebra.IntegralMixedFramedCompanionObservationFrom
/-! # One natural tuple for the complete physical retained-endpoint level -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedChronologicalFrame IntegralMixedPointCompanion IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" r=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (e :ℕ) (he :e<IntegralMixedRoadmapAtomic.endBirth
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old)
local notation "r"=>preparedRoot hn ht ha hR0 old e
local notation "older"=>parentCommands hn ht ha hR0 old hv hd e he
local notation "d"=>parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "a"=>endpointLabel hn ht ha hR0 old hv hd e he
local notation "F"=>IntegralMixedChronologicalMidpoint.frame d hk a a
local notation "g"=>midpointObjective hn ht ha hR0 old hv hd e he
local notation "js"=>midpointSelections hn ht ha hR0 old hv hd e he
local notation "dc"=>childDescriptor hn ht ha hR0 old hv hd e he
local notation "gc"=>childObjective hn ht ha hR0 old hv hd e he
local notation "cs"=>childSelections hn ht ha hR0 old hv hd e he
local notation "hQ"=>IntegralMixedStaticRecordPrefix.cap (Q r) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r)

noncomputable def midpointPast:=midpointInstructions hn ht ha hR0 old hv hd e he++older
theorem midpoint_past_room :(midpointPast hn ht ha hR0 old hv hd e he).length≤(P).cap r+1+1:=by
  have HR:=midpoint_room hn ht ha hR0 old hv hd e he
  simp only [midpointPast,List.length_append,midpointInstructions,List.length_map,midpointCommands,commands_length]
  omega
theorem midpoint_past_birth :(midpointPast hn ht ha hR0 old hv hd e he).length=(older).length+(js).length:=by
  simp only [midpointPast,List.length_append,midpointInstructions,List.length_map,midpointCommands,commands_length]
  omega

noncomputable def midpointColumns:=IntegralMixedPointCompanion.columns («P»:=Q r) (B:=(P).width r)
  (F).frozen (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk))
  (IntegralMixedChronologicalMidpoint.rows d hk a a) g (enumerate older) js

theorem midpoint_arity :arity (midpointPast hn ht ha hR0 old hv hd e he)=arity older+(2*(P).ambient r+4)*(js).length:=by
  exact IntegralMixedFramedFixedContinuation.companion_arity hQ older (F).frozen
    (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk)) (IntegralMixedChronologicalMidpoint.rows d hk a a) g js

theorem midpoint_index :Index (Fin 0) (midpointPast hn ht ha hR0 old hv hd e he)=
    IntegralMixedFullHistoryScript.Index (Index (Fin 0) older) (midpointCommands hn ht ha hR0 old hv hd e he):=
  IntegralMixedFramedFixedContinuation.index_append (Q r) hQ (midpointCommands hn ht ha hR0 old hv hd e he) older

theorem midpoint_enumerate :HEq (enumerate (midpointPast hn ht ha hR0 old hv hd e he))
    (midpointColumns hn ht ha hR0 old hv hd e he):=
  IntegralMixedFramedFixedContinuation.companion_columns hQ older (F).frozen
    (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk)) (IntegralMixedChronologicalMidpoint.rows d hk a a) g js

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedExceptionalBounds.auxiliaryCap
  preparedRoot parentCommands parentDescriptor midpointObjective endpointLabel

theorem midpoint_column_old (i :Index (Fin 0) older) :
    (midpointColumns hn ht ha hR0 old hv hd e he
      (IntegralMixedOptionalEndpoints.oldColumns (midpointCommands hn ht ha hR0 old hv hd e he) i)).val=
      (enumerate older i).val:=by
  unfold midpointColumns
  exact @IntegralMixedPointCompanion.columns_old ((P).ambient r) ((P).width r) (older).length
    (Q r) (Index (Fin 0) older) (F).frozen
    (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk))
    (IntegralMixedChronologicalMidpoint.rows d hk a a) g (arity older) (enumerate older) js i

theorem midpoint_column_block (k :Fin (js).length) (i :Fin ((P).ambient r+1)) :
    (midpointColumns hn ht ha hR0 old hv hd e he
      (blockColumn («P»:=Q r) (B:=(P).width r) (F).frozen
        (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk))
        (IntegralMixedChronologicalMidpoint.rows d hk a a) g js k i)).val=
      arity older+(2*(P).ambient r+4)*((js).length-1-k.val)+i.val:=by
  unfold midpointColumns
  exact @IntegralMixedPointCompanion.columns_block ((P).ambient r) ((P).width r) (older).length
    (Q r) (Index (Fin 0) older) (F).frozen
    (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk))
    (IntegralMixedChronologicalMidpoint.rows d hk a a) g (arity older) (enumerate older) js k i

theorem midpoint_state :HEq
    (reframe (run (initial P D r) (midpointPast hn ht ha hR0 old hv hd e he)
      (midpoint_past_room hn ht ha hR0 old hv hd e he)) (Q r) hQ)
    (midpointState hn ht ha hR0 old hv hd e he):=by
  have HA:=IntegralMixedFramedFixedContinuation.run_append (initial P D r) (Q r) hQ older
    (parent_room hn ht ha hR0 old hv hd e he)
    (commands («P»:=Q r) (B:=(P).width r) (F).frozen (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk))
      (IntegralMixedChronologicalMidpoint.rows d hk a a) g js)
    (by simpa only [commands_length] using midpoint_room hn ht ha hR0 old hv hd e he)
  have HC:=IntegralMixedPointCompanion.run_continue (parentState hn ht ha hR0 old hv hd e he) (F).frozen
    (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk)) (IntegralMixedChronologicalMidpoint.rows d hk a a) g js
    (midpoint_room hn ht ha hR0 old hv hd e he)
  unfold parentState at HC
  simpa only [midpointState,midpointPast,midpointInstructions,midpointCommands,parentState] using HA.trans HC.symm

noncomputable def childCommands :List (IntegralMixedFullHistoryScript.Command (Q r) ((P).width r)):=
  commands (dc).frame.frozen (fun _=>false) (fun i=>.single ((dc).atom i)) gc cs
noncomputable def childInstructions :List (Instruction ((P).ambient r) ((P).width r)):=
  (childCommands hn ht ha hR0 old hv hd e he).map (IntegralMixedFramedFixedContinuation.wrap (Q r) hQ)
noncomputable def localInstructions :List (Instruction ((P).ambient r) ((P).width r)):=
  childInstructions hn ht ha hR0 old hv hd e he++midpointPast hn ht ha hR0 old hv hd e he
theorem local_room :(localInstructions hn ht ha hR0 old hv hd e he).length≤(P).cap r+1+1:=by
  have HR:=child_room hn ht ha hR0 old hv hd e he
  simp only [localInstructions,childInstructions,List.length_append,List.length_map,childCommands,commands_length,midpoint_past_birth]
  omega

attribute [local irreducible] parentState parentTuple parentValues
  childDescriptor childObjective midpointCommands midpointInstructions midpointColumns
  IntegralMixedFramedHistoryScript.Index IntegralMixedFramedRunObservation.ofCommands

theorem exists_local_tuple (p :Fin ((P).ambient r+1)→ℝ)
    (hp :p∈slice (Q r) (d).frame (parentValues hn ht ha hR0 old hv hd e he))
    (hheight :p (IntegralMixedChronologicalMidpoint.next d hk)=
      parentValues hn ht ha hR0 old hv hd e he (IntegralMixedChronologicalMidpoint.reference a))
    (hg :∀i,i∉(F).frozen→i≠(g).val→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂ (Int.castRingHom ℝ) p=0):
    ∃u :ℕ→ℝ,(IntegralMixedFramedRunObservation.ofCommands (initial P D r)
      (localInstructions hn ht ha hR0 old hv hd e he) (local_room hn ht ha hR0 old hv hd e he)).Roots u ∧
    (∀i,i<arity older→u i=oldNatural hn ht ha hR0 old hv i) ∧
    (∀k :Fin (js).length,∀i,
      u (arity older+(2*(P).ambient r+4)*((js).length-1-k.val)+i.val)^
        UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r)
          ((older).length+((js).length-1-k.val))=p i) ∧
    (∀k :Fin (cs).length,∀i,
      u (arity older+(2*(P).ambient r+4)*(js).length+(2*(P).ambient r+4)*((cs).length-1-k.val)+i.val)^
        UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r)
          ((older).length+(js).length+((cs).length-1-k.val))=p i) ∧
    ∀i :Fin ((older).length+(js).length+(cs).length),
      (IntegralMixedFramedRunObservation.ofCommands (initial P D r) (localInstructions hn ht ha hR0 old hv hd e he)
        (local_room hn ht ha hR0 old hv hd e he)).point u i.val=
          values p (values p (parentValues hn ht ha hR0 old hv hd e he) js) cs i:=by
  have H:=exists_local_blocks hn ht ha hR0 old hv hd e he p hp hheight hg
  let φ:=Classical.choose H
  let RM:=Classical.choose (Classical.choose_spec H)
  let RC:=Classical.choice (Classical.choose_spec (Classical.choose_spec H))
  have HI:=midpoint_index hn ht ha hR0 old hv hd e he
  simp only [midpointCommands] at HI
  have HM:=midpoint_past_birth hn ht ha hR0 old hv hd e he
  have HS:=midpoint_state hn ht ha hR0 old hv hd e he
  have HL:=midpoint_arity hn ht ha hR0 old hv hd e he
  have HE:=midpoint_enumerate hn ht ha hR0 old hv hd e he
  have HO:=@IntegralMixedFramedFixedContinuation.companion_observation_from
    ((P).ambient r) ((P).cap r+1) ((P).width r) ((older).length+(js).length)
    (arity older+(2*(P).ambient r+4)*(js).length) _ (Q r) _ _
    (initial P D r) hQ (midpointPast hn ht ha hR0 old hv hd e he) (midpoint_past_room hn ht ha hR0 old hv hd e he)
    (midpointState hn ht ha hR0 old hv hd e he) HI HM HS (midpointColumns hn ht ha hR0 old hv hd e he) HL HE
    (dc).frame.frozen (fun _=>false) (fun i=>.single ((dc).atom i)) gc RM.tuple RM.hom
    (values p (parentValues hn ht ha hR0 old hv hd e he) js) p cs (child_room hn ht ha hR0 old hv hd e he) RC
  obtain ⟨u,HU,Hraw,Hblocks,Hpoint⟩:=HO
  refine ⟨u,?_,?_,?_,Hblocks,?_⟩
  · convert HU using 1; rfl
  · intro i hi
    let j:=(enumerate older).symm ⟨i,hi⟩
    have HC:=Hraw (IntegralMixedOptionalEndpoints.oldColumns (commands («P»:=Q r) (B:=(P).width r)
      (F).frozen (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk))
      (IntegralMixedChronologicalMidpoint.rows d hk a a) g js) j)
    have HCol:=midpoint_column_old hn ht ha hR0 old hv hd e he j
    have HC' :u (enumerate older j).val=RM.tuple
        (IntegralMixedOptionalEndpoints.oldColumns (commands («P»:=Q r) (B:=(P).width r)
          (F).frozen (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk))
          (IntegralMixedChronologicalMidpoint.rows d hk a a) g js) j):=by
      apply Eq.trans (congrArg u HCol.symm)
      convert HC using 1; unfold midpointCommands; rfl
    have HT:=HC'.trans (RM.old_raw j)
    simpa only [parentTuple,j,Equiv.apply_symm_apply] using HT
  · intro k i
    have HC:=Hraw (blockColumn («P»:=Q r) (B:=(P).width r) (F).frozen
      (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk))
      (IntegralMixedChronologicalMidpoint.rows d hk a a) g js k i)
    have HCol:=midpoint_column_block hn ht ha hR0 old hv hd e he k i
    have HC' :u (arity older+(2*(P).ambient r+4)*((js).length-1-k.val)+i.val)=
        RM.tuple (blockColumn («P»:=Q r) (B:=(P).width r) (F).frozen
          (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk))
          (IntegralMixedChronologicalMidpoint.rows d hk a a) g js k i):=by
      apply Eq.trans (congrArg u HCol.symm)
      convert HC using 1
    rw [HC']
    exact RM.blocks k i
  · convert Hpoint using 1; rfl

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend

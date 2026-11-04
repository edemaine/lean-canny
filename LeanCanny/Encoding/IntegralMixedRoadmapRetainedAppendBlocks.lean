/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendProgram
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendBounds
/-! # Actual midpoint blocks at the appended parent, with every raw column

The complete block includes its anchor. Its tuple is constructed on the
actual final horizon/width; no old complete ordinal or interpretation is an
input. Child and padding blocks can retain this same natural tuple.
-/
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

theorem parent_descriptor_length :(d).labels.length=IntegralMixedRoadmapAtomic.depth old:=by
  simp only [parentDescriptor,IntegralMixedChronologicalFrameCode.descriptor_length,IntegralMixedRoadmapAtomic.frozen_count]

theorem parent_descriptor_nonterminal :(d).labels.length<(P).ambient r:=by
  rw [parent_descriptor_length,prepared_dimension]
  exact hd

theorem parent_descriptor_fit :(d).labels.length<(P).ambient r+1:=
  (parent_descriptor_nonterminal hn ht ha hR0 old hv hd e he).trans (Nat.lt_succ_self _)

noncomputable def endpointLabel :Fin (older).length:=⟨e,by rw [parent_length];exact he⟩

noncomputable def parentValues :Fin (older).length→ℝ:=
  IntegralMixedFullBankPoint.point (parentState hn ht ha hR0 old hv hd e he)
    (parentTuple hn ht ha hR0 old hv hd e he)

local notation "hk"=>parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "a"=>endpointLabel hn ht ha hR0 old hv hd e he
local notation "F"=>IntegralMixedChronologicalMidpoint.frame d hk a a

noncomputable def midpointObjective :Free (F).frozen:=
  ⟨⟨(d).labels.length+1,by have H:=parent_descriptor_nonterminal hn ht ha hR0 old hv hd e he;omega⟩,
    (IntegralMixedChronologicalMidpoint.free_iff d hk a a _).mpr (Nat.le_refl _)⟩

local notation "g"=>midpointObjective hn ht ha hR0 old hv hd e he
noncomputable def midpointSelections:=IntegralMixedChronologicalMidpointSignature.orderedFree d hk a a++[g]
noncomputable def midpointCommands :List (IntegralMixedFullHistoryScript.Command (Q r) ((P).width r)):=
  IntegralMixedPointCompanion.commands (F).frozen (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk))
    (IntegralMixedChronologicalMidpoint.rows d hk a a) g (midpointSelections hn ht ha hR0 old hv hd e he)

noncomputable def midpointInstructions :List (Instruction ((P).ambient r) ((P).width r)):=
  (midpointCommands hn ht ha hR0 old hv hd e he).map
    (IntegralMixedFramedFixedContinuation.wrap (Q r) (IntegralMixedStaticRecordPrefix.cap (Q r)
      (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r)))

theorem midpoint_selection_count :(midpointSelections hn ht ha hR0 old hv hd e he).length=
    IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old-IntegralMixedRoadmapAtomic.depth old+1:=by
  simp only [midpointSelections,List.length_append,List.length_singleton,
    IntegralMixedChronologicalMidpointSignature.orderedFree_length,IntegralMixedChronologicalMidpointSignature.freeCount,
    parent_descriptor_length,prepared_dimension]
  omega

theorem midpoint_room :(older).length+(midpointSelections hn ht ha hR0 old hv hd e he).length≤(P).cap r+1+1:=by
  rw [midpoint_selection_count,parent_length]
  have HF:=finish_le_full hn ht ha hR0 old hv hd e he
  simp only [finish_eq,beginBirth] at HF
  have HB :fullBirth hn ht ha hR0 old e≤(P).cap r+1:=
    IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 r _ (Nat.le_refl _)
  omega

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedExceptionalBounds.auxiliaryCap
  preparedRoot start parentCommands parentState parentTuple parentDescriptor parentValues
  midpointCommands midpointInstructions midpointObjective endpointLabel
  IntegralMixedFramedHistoryScript.Index IntegralMixedFramedRunObservation.ofCommands
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth

theorem exists_midpoint_tuple (p :Fin ((P).ambient r+1)→ℝ)
    (hp :p∈slice (Q r) (d).frame (parentValues hn ht ha hR0 old hv hd e he))
    (hheight :p (IntegralMixedChronologicalMidpoint.next d hk)=
      parentValues hn ht ha hR0 old hv hd e he (IntegralMixedChronologicalMidpoint.reference a))
    (hgradient :∀i,i∉(F).frozen→i≠(g).val→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) p=0):
    ∃v :ℕ→ℝ,
      (IntegralMixedFramedRunObservation.ofCommands (initial P D r)
        (midpointInstructions hn ht ha hR0 old hv hd e he++older)
        (by have HR:=midpoint_room hn ht ha hR0 old hv hd e he
            simp only [midpointInstructions,midpointCommands,List.length_append,List.length_map,commands_length];omega)).Roots v ∧
      (∀i,i<arity older→v i=oldNatural hn ht ha hR0 old hv i) ∧
      (∀k :Fin (midpointSelections hn ht ha hR0 old hv hd e he).length,∀i,
        v (arity older+(2*(P).ambient r+4)*
          ((midpointSelections hn ht ha hR0 old hv hd e he).length-1-k.val)+i.val)^
            UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r)
              ((older).length+((midpointSelections hn ht ha hR0 old hv hd e he).length-1-k.val))=p i) ∧
      ∀i :Fin ((older).length+(midpointSelections hn ht ha hR0 old hv hd e he).length),
        (IntegralMixedFramedRunObservation.ofCommands (initial P D r)
          (midpointInstructions hn ht ha hR0 old hv hd e he++older)
          (by have HR:=midpoint_room hn ht ha hR0 old hv hd e he
              simp only [midpointInstructions,midpointCommands,List.length_append,List.length_map,commands_length];omega)).point v i.val=
          values p (parentValues hn ht ha hR0 old hv hd e he)
            (midpointSelections hn ht ha hR0 old hv hd e he) i:=by
  have room:=midpoint_room hn ht ha hR0 old hv hd e he
  let x:=reframe (run (initial P D r) older (parent_room hn ht ha hR0 old hv hd e he)) (Q r)
    (IntegralMixedStaticRecordPrefix.cap (Q r) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r))
  have HI:=parent_interpretation hn ht ha hR0 old hv hd e he
  unfold parentState at HI
  obtain ⟨φ,hφ,H⟩:=HI
  have HZ :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) (parentTuple hn ht ha hR0 old hv hd e he)=0:=by
    simpa only [x,parentState] using parent_roots hn ht ha hR0 old hv hd e he
  have HH :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=parentValues hn ht ha hR0 old hv hd e he i:=by
    simpa only [x,parentValues,parentState] using H
  have Hdegree :(Q r).degree=BoundedZeroSource.powerDegree
      (t (IntegralMixedAuxiliaryMarkedIntegerSource.original r)).toData.size:=
    IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t (radius R0) r
  have HM :p (IntegralMixedChronologicalMidpoint.next d hk)=
      (parentValues hn ht ha hR0 old hv hd e he (IntegralMixedChronologicalMidpoint.reference a)+
       parentValues hn ht ha hR0 old hv hd e he (IntegralMixedChronologicalMidpoint.reference a))/2:=by
    rw [hheight]
    ring
  have roomG :(older).length+(IntegralMixedChronologicalMidpointSignature.orderedFree d hk a a++[g]).length≤
      (P).cap r+1+1:=by simpa only [midpointSelections] using room
  have HC:=@exists_midpoint_block ((P).ambient r) ((P).cap r+1) ((P).width r) (older).length (Q r)
    (Index (Fin 0) older) (indexFintype (Fin 0) older)
    x d hk a a g (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha r)
    _ Hdegree (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r)
    (parentTuple hn ht ha hR0 old hv hd e he) HZ
    φ hφ (parentValues hn ht ha hR0 old hv hd e he) HH p hp HM hgradient roomG
  obtain ⟨R⟩:=HC
  obtain ⟨v,HV,Hold,Hblocks,Hpoint⟩:=@IntegralMixedFramedFixedContinuation.companion_observation
    ((P).ambient r) ((P).width r) (Q r)
    ((P).ambient r) ((P).cap r+1) ((P).width r) ((D).initialSource r)
    (initial P D r) (Q r) (IntegralMixedStaticRecordPrefix.cap (Q r)
      (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r)) older (parent_room hn ht ha hR0 old hv hd e he)
    (F).frozen (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk))
    (IntegralMixedChronologicalMidpoint.rows d hk a a) g (parentTuple hn ht ha hR0 old hv hd e he)
    φ (parentValues hn ht ha hR0 old hv hd e he) p (midpointSelections hn ht ha hR0 old hv hd e he) room R
  refine ⟨v,?_,?_,Hblocks,?_⟩
  · simpa only [midpointInstructions,midpointCommands] using HV
  · intro i hi
    have HH:=Hold ((enumerate older).symm ⟨i,hi⟩)
    simpa only [Equiv.apply_symm_apply,parentTuple] using HH
  · simpa only [midpointInstructions,midpointCommands] using Hpoint

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend

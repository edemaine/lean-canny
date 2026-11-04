/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPadding
public import LeanCanny.Encoding.IntegralMixedMarkedSeedTailRetained
/-! # Fresh own-context full words retain both appended physical blocks -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedPointCompanion IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
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
local notation "cs"=>childSelections hn ht ha hR0 old hv hd e he
local notation "localCs"=>localInstructions hn ht ha hR0 old hv hd e he
local notation "tailCount"=>seedTailCount hn ht ha hR0 old e
local notation "CTX"=>pair r []

theorem retained_input_eq :IntegralMixedMarkedReservedParent.input hn ht ha hR0=S:=by
  unfold IntegralMixedMarkedReservedParent.input IntegralMixedMarkedReservedParent.bank
    IntegralMixedPhysicalMarkedTest.input IntegralMixedPhysicalMarkedPlan.bank
  rfl

theorem retained_valid_to_parent (c w :List Bool) (hw :SquareSampleCompleteVertices.Valid S c w):
    SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0) c w:=
  Eq.mp (congrArg (fun I=>SquareSampleCompleteVertices.Valid I c w)
    (retained_input_eq hn ht ha hR0).symm) hw

private theorem sample_full (root :List Bool) (u :ℕ→ℝ)
    (hu :(IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 root).Roots u):
    IntegralMixedMarkedSeedTailRetained.Sampled hn ht ha hR0 root u:=by
  have HE :IntegralMixedMarkedSeedTailRetained.fullObservation hn ht ha hR0 root=
      IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 root:=by
    unfold IntegralMixedMarkedSeedTailRetained.fullObservation
      IntegralMixedMarkedPrefixFieldReadback.fullObservation IntegralMixedMarkedReservedParent.bank
    rfl
  have HC:=IntegralMixedMarkedReservedParent.full_prefix hn ht ha hR0 root
  rw [←IntegralMixedMarkedPrefixFieldReadback.rules_length hn ht ha hR0] at HC
  apply IntegralMixedMarkedSeedTailRetained.sample_observation hn ht ha hR0 root u
  · exact Eq.mpr (congrArg (fun O:IntegralMixedFramedRunObservation.Data=>O.Roots u) HE) hu
  · have HR :((B).plan.rules root).length=
        ((IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)).rules root).length:=by
      unfold IntegralMixedMarkedReservedParent.bank
      rfl
    exact HC.trans HR.symm

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap preparedRoot parentCommands parentDescriptor parentValues
  midpointObjective endpointLabel localInstructions localObservation
  IntegralMixedMarkedPrefixFieldReadback.fullObservation

structure WordReceipt (p p0 :Fin ((P).ambient r+1)→ℝ) where
  localTuple :ℕ→ℝ
  tuple :ℕ→ℝ
  word :List Bool
  valid :SquareSampleCompleteVertices.Valid S CTX word
  word_length :word.length=SquareSampleCompleteVertices.width S CTX
  joint :∀i :Fin (IntegralFramedPhysicalSquare.count (B).parameters (B).plan ((B).key CTX)),
    IntegralFramedPhysicalSquare.joint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed
      (B).bounds (B).key (B).positive CTX word (retained_valid_to_parent hn ht ha hR0 _ _ valid) i=tuple i.val
  local_roots :(localObservation hn ht ha hR0 old hv hd e he).Roots localTuple
  old_raw :∀i,i<arity older→localTuple i=oldNatural hn ht ha hR0 old hv i
  midpoint_blocks :∀k :Fin (js).length,∀i,
    localTuple (arity older+(2*(P).ambient r+4)*((js).length-1-k.val)+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r)
        ((older).length+((js).length-1-k.val))=p i
  child_blocks :∀k :Fin (cs).length,∀i,
    localTuple (arity older+(2*(P).ambient r+4)*(js).length+(2*(P).ambient r+4)*((cs).length-1-k.val)+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r)
        ((older).length+(js).length+((cs).length-1-k.val))=p i
  local_values :∀i :Fin ((older).length+(js).length+(cs).length),
    (localObservation hn ht ha hR0 old hv hd e he).point localTuple i.val=
      values p (values p (parentValues hn ht ha hR0 old hv hd e he) js) cs i
  roots :(IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 r).Roots tuple
  preserved :∀i,i<arity localCs→tuple i=localTuple i
  padding_blocks :∀j :Fin (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient r) tailCount).length,∀i,
    tuple (arity localCs+(2*(P).ambient r+4)*((IntegralMixedCanonicalPadding.paddingSelections ((P).ambient r) tailCount).length-1-j.val)+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r)
        ((localCs).length+((IntegralMixedCanonicalPadding.paddingSelections ((P).ambient r) tailCount).length-1-j.val))=p0 i
  values :∀i :Fin ((localCs).length+(IntegralMixedCanonicalPadding.paddingSelections ((P).ambient r) tailCount).length),
    (IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 r).point tuple i.val=
      IntegralMixedPointCompanion.values p0
        (fun j=>(localObservation hn ht ha hR0 old hv hd e he).point localTuple j.val)
        (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient r) tailCount) i



theorem exists_word_receipt (p :Fin ((P).ambient r+1)→ℝ)
    (hp :p∈slice (Q r) (d).frame (parentValues hn ht ha hR0 old hv hd e he))
    (hheight :p (IntegralMixedChronologicalMidpoint.next d hk)=
      parentValues hn ht ha hR0 old hv hd e he (IntegralMixedChronologicalMidpoint.reference a))
    (hg :∀i,i∉(F).frozen→i≠(g).val→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂ (Int.castRingHom ℝ) p=0)
    (p0 :Fin ((P).ambient r+1)→ℝ)
    (hp0 :(FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree).eval₂
      (Int.castRingHom ℝ) p0=0)
    (hg0 :∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) p0=0):
    Nonempty (WordReceipt hn ht ha hR0 old hv hd e he p p0):=by
  obtain ⟨z,HZ,HO,HM,HC,HV⟩:=exists_local_tuple hn ht ha hR0 old hv hd e he p hp hheight hg
  have HZ' :(localObservation hn ht ha hR0 old hv hd e he).Roots z:=by
    simpa only [localObservation] using HZ
  have HV' :∀i :Fin ((older).length+(js).length+(cs).length),
      (localObservation hn ht ha hR0 old hv hd e he).point z i.val=
        values p (values p (parentValues hn ht ha hR0 old hv hd e he) js) cs i:=by
    simpa only [localObservation] using HV
  obtain ⟨u,HU,HK,HP,HF⟩:=pad_local_tuple hn ht ha hR0 old hv hd e he z HZ' p0 hp0 hg0
  obtain ⟨w,hw,hlen,HJ⟩:=sample_full hn ht ha hR0 r u HU
  have hwS :SquareSampleCompleteVertices.Valid S CTX w:=Eq.mp
    (congrArg (fun I=>SquareSampleCompleteVertices.Valid I CTX w) (retained_input_eq hn ht ha hR0)) hw
  refine ⟨⟨z,u,w,hwS,?_,HJ,HZ',HO,HM,HC,HV',HU,HK,HP,HF⟩⟩
  simpa only [retained_input_eq hn ht ha hR0,IntegralMixedMarkedReservedParent.context] using hlen

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend

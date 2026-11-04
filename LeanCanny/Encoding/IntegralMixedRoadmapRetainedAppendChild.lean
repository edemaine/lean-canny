/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendBlocks
/-! # The child block preserves the complete midpoint realization -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedChronologicalFrame IntegralMixedChronologicalEndpoint IntegralMixedPointCompanion IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem retained_slice_values {n birth :ℕ} (D :Descriptor n birth) (V :SpatialSource n)
    {frozen :Finset (Fin (n+1))} (p :Fin (n+1)→ℝ) (old :Fin birth→ℝ) (js :List (Free frozen)):
    slice V (retainMany D js.length).frame (values p old js)=slice V D.frame old:=by
  induction js with
  | nil=>rfl
  | cons j js ih=>
    change slice V ((retainMany D js.length).retain).frame (Fin.cons (p j.val) (values p old js))=_
    rw [Descriptor.frame_retain,slice_retained]
    exact ih

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
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

noncomputable def midpointState:=IntegralMixedPointCompanion.run (parentState hn ht ha hR0 old hv hd e he)
  (F).frozen (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk))
  (IntegralMixedChronologicalMidpoint.rows d hk a a) g js (midpoint_room hn ht ha hR0 old hv hd e he)

noncomputable def childDescriptor:=retainMany ((d).freeze a hk) (js).length

noncomputable def childObjective :Free (childDescriptor hn ht ha hR0 old hv hd e he).frame.frozen:=
  ⟨(g).val,by
    rw [Descriptor.frozen_mem,childDescriptor,retainMany_length,Descriptor.freeze_length]
    change ¬((d).labels.length+1<(d).labels.length+1)
    omega⟩

noncomputable def childSelections:=(childDescriptor hn ht ha hR0 old hv hd e he).orderedFree++
  [childObjective hn ht ha hR0 old hv hd e he]

theorem child_selection_count :(childSelections hn ht ha hR0 old hv hd e he).length=
    IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old-IntegralMixedRoadmapAtomic.depth old+1:=by
  simp only [childSelections,List.length_append,List.length_singleton,Descriptor.orderedFree_length,
    Descriptor.freeCount,childDescriptor,retainMany_length,Descriptor.freeze_length,parent_descriptor_length,
    prepared_dimension]
  omega

theorem child_room :(older).length+(js).length+(childSelections hn ht ha hR0 old hv hd e he).length≤(P).cap r+1+1:=by
  rw [child_selection_count,midpoint_selection_count,parent_length]
  have HF:=finish_le_full hn ht ha hR0 old hv hd e he
  simp only [finish_eq,beginBirth] at HF
  have HB :fullBirth hn ht ha hR0 old e≤(P).cap r+1:=
    IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 r _ (Nat.le_refl _)
  omega

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedExceptionalBounds.auxiliaryCap
  preparedRoot start parentCommands parentTuple parentDescriptor parentValues midpointObjective endpointLabel
  childDescriptor childSelections childObjective IntegralMixedFramedHistoryScript.Index

theorem child_slice (p :Fin ((P).ambient r+1)→ℝ)
    (hp :p∈slice (Q r) (d).frame (parentValues hn ht ha hR0 old hv hd e he))
    (hheight :p (IntegralMixedChronologicalMidpoint.next d hk)=
      parentValues hn ht ha hR0 old hv hd e he (IntegralMixedChronologicalMidpoint.reference a)):
    p∈slice (Q r) (childDescriptor hn ht ha hR0 old hv hd e he).frame
      (values p (parentValues hn ht ha hR0 old hv hd e he) js):=by
  rw [childDescriptor,retained_slice_values,Descriptor.freeze_slice]
  exact ⟨hp,hheight⟩

theorem child_gradient (p :Fin ((P).ambient r+1)→ℝ)
    (hg :∀i,i∉(F).frozen→i≠(g).val→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) p=0):
    ∀i,i∉(childDescriptor hn ht ha hR0 old hv hd e he).frame.frozen→
      i≠(childObjective hn ht ha hR0 old hv hd e he).val→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) p=0:=by
  intro i hi hne
  have HF :i∉(F).frozen:=by
    rw [IntegralMixedChronologicalMidpoint.frozen_mem]
    simpa only [Descriptor.frozen_mem,childDescriptor,retainMany_length,Descriptor.freeze_length] using hi
  apply hg i HF
  simpa only [childObjective] using hne

theorem exists_local_blocks (p :Fin ((P).ambient r+1)→ℝ)
    (hp :p∈slice (Q r) (d).frame (parentValues hn ht ha hR0 old hv hd e he))
    (hheight :p (IntegralMixedChronologicalMidpoint.next d hk)=
      parentValues hn ht ha hR0 old hv hd e he (IntegralMixedChronologicalMidpoint.reference a))
    (hg :∀i,i∉(F).frozen→i≠(g).val→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) p=0):
    ∃φ :(parentState hn ht ha hR0 old hv hd e he).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    ∃R :Realized (parentState hn ht ha hR0 old hv hd e he) (F).frozen
      (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk)) (IntegralMixedChronologicalMidpoint.rows d hk a a) g
      (parentTuple hn ht ha hR0 old hv hd e he) φ (parentValues hn ht ha hR0 old hv hd e he) p js
      (midpoint_room hn ht ha hR0 old hv hd e he),
    Nonempty (Realized (midpointState hn ht ha hR0 old hv hd e he)
      (childDescriptor hn ht ha hR0 old hv hd e he).frame.frozen (fun _=>false)
      (fun i=>.single ((childDescriptor hn ht ha hR0 old hv hd e he).atom i))
      (childObjective hn ht ha hR0 old hv hd e he) R.tuple R.hom
      (values p (parentValues hn ht ha hR0 old hv hd e he) js) p (childSelections hn ht ha hR0 old hv hd e he)
      (child_room hn ht ha hR0 old hv hd e he)):=by
  let HI:=parent_interpretation hn ht ha hR0 old hv hd e he
  let φ:=Classical.choose HI
  have hφ:=(Classical.choose_spec HI).1
  have H:=(Classical.choose_spec HI).2
  have HV :∀i,φ ((parentState hn ht ha hR0 old hv hd e he).bank.numerator i)/
      ((parentState hn ht ha hR0 old hv hd e he).bank.denominator i:ℝ)=parentValues hn ht ha hR0 old hv hd e he i:=by
    simpa only [parentValues] using H
  have Hdegree :(Q r).degree=BoundedZeroSource.powerDegree
      (t (IntegralMixedAuxiliaryMarkedIntegerSource.original r)).toData.size:=
    IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t (radius R0) r
  have HM :p (IntegralMixedChronologicalMidpoint.next d hk)=
      (parentValues hn ht ha hR0 old hv hd e he (IntegralMixedChronologicalMidpoint.reference a)+
       parentValues hn ht ha hR0 old hv hd e he (IntegralMixedChronologicalMidpoint.reference a))/2:=by
    rw [hheight]
    ring
  have HMroom :(older).length+(IntegralMixedChronologicalMidpointSignature.orderedFree d hk a a++[g]).length≤
      (P).cap r+1+1:=by simpa only [midpointSelections] using midpoint_room hn ht ha hR0 old hv hd e he
  have HMid:=@exists_midpoint_block ((P).ambient r) ((P).cap r+1) ((P).width r) (older).length (Q r)
    (Index (Fin 0) older) (indexFintype (Fin 0) older)
    (parentState hn ht ha hR0 old hv hd e he) d hk a a g (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha r)
    _ Hdegree (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r)
    (parentTuple hn ht ha hR0 old hv hd e he) (parent_roots hn ht ha hR0 old hv hd e he)
    φ hφ (parentValues hn ht ha hR0 old hv hd e he) HV p hp HM hg HMroom
  let R:=Classical.choice HMid
  refine ⟨φ,R,?_⟩
  have HCroom :(older).length+(js).length+
      ((childDescriptor hn ht ha hR0 old hv hd e he).orderedFree++[childObjective hn ht ha hR0 old hv hd e he]).length≤
      (P).cap r+1+1:=by simpa only [childSelections] using child_room hn ht ha hR0 old hv hd e he
  have HC:=exists_atomic_block (midpointState hn ht ha hR0 old hv hd e he)
    (childDescriptor hn ht ha hR0 old hv hd e he) (childObjective hn ht ha hR0 old hv hd e he)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha r) _ Hdegree
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r) R.tuple R.roots R.hom R.generators
    (values p (parentValues hn ht ha hR0 old hv hd e he) js) R.quotients p
    (child_slice hn ht ha hR0 old hv hd e he p hp hheight)
    (child_gradient hn ht ha hR0 old hv hd e he p hg) HCroom
  simpa only [childSelections] using HC

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend

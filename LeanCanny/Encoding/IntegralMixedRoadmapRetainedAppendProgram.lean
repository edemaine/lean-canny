/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendParent
public import LeanCanny.Geometry.IntegralMixedChronologicalRetainedLevel
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameDecode
/-! # The concrete retained level uses the actual frozen producer descriptor -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedChronologicalFrame
open IntegralMixedPointCompanion IntegralMixedFrozenFrame IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem descriptor_frozen_labels (d birth :ℕ) (q :List Bool) (k :ℕ)
    (H :IntegralMixedChronologicalFrameCode.Good d birth (IntegralMixedRoadmapChain.frozen q k)):
    IntegralMixedChronologicalFrameCode.labels (IntegralMixedChronologicalFrameCode.descriptor d birth
      (IntegralMixedRoadmapChain.frozen q k) H)=IntegralMixedRoadmapChain.frozen q k:=by
  change WordList.encode ((IntegralMixedChronologicalFrameCode.descriptor d birth
    (IntegralMixedRoadmapChain.frozen q k) H).labels.map (fun i=>BinaryNatCode.encode i.val))=_
  conv_rhs=>rw [IntegralMixedRoadmapChain.frozen]
  apply congrArg WordList.encode
  apply List.ext_getElem
  · simp only [IntegralMixedChronologicalFrameCode.descriptor,List.length_map,List.length_ofFn,
      IntegralMixedRoadmapChain.frozen_count,List.length_range]
  · intro i hi hj
    have HI :i<k:=by simpa only [IntegralMixedChronologicalFrameCode.descriptor,List.length_map,
      List.length_ofFn,IntegralMixedRoadmapChain.frozen_count] using hi
    simp only [IntegralMixedChronologicalFrameCode.descriptor,List.getElem_map,List.getElem_ofFn,
      IntegralMixedRoadmapChain.frozen_lookup q k i HI,List.getElem_range]

private theorem block_codes_map {d birth :ℕ} (frozen :Finset (Fin (d+1))) (double :Fin (d+1)→Bool)
    (rows :Fin (d+1)→Row birth) (g :Free frozen) (js :List (Free frozen)):
    IntegralMixedPointCompanion.codes frozen double rows g js=
      js.map (fun j=>(pointData frozen double rows g 0 j).code):=by
  induction js with
  | nil=>rfl
  | cons j js ih=>rw [IntegralMixedPointCompanion.codes,List.map_cons,pointData_code_stable,ih]

theorem block_codes_anchor {d birth :ℕ} (frozen :Finset (Fin (d+1))) (double :Fin (d+1)→Bool)
    (rows :Fin (d+1)→Row birth) (g :Free frozen) (js :List (Free frozen)):
    IntegralMixedPointCompanion.codes frozen double rows g (js++[g])=
      IntegralMixedPointCompanion.codes frozen double rows g js++[(pointData frozen double rows g 0 g).code]:=by
  rw [block_codes_map,List.map_append,List.map_singleton,←block_codes_map]

theorem atomic_block_codes {d birth :ℕ} (D :Descriptor d birth) (g :Free D.frame.frozen):
    (IntegralMixedPointCompanion.codes D.frame.frozen (fun _=>false) (fun i=>.single (D.atom i))
      g (D.orderedFree++[g])).reverse=
      [IntegralMixedChronologicalFrameCode.code d (IntegralMixedChronologicalFrameCode.labels D) g.val.val g.val.val]++
        IntegralMixedChronologicalCompanionCode.codes d (IntegralMixedChronologicalFrameCode.labels D) g.val.val:=by
  have HA :(pointData D.frame.frozen (fun _=>false) (fun i=>.single (D.atom i)) g 0 g).code=
      IntegralMixedChronologicalFrameCode.code d (IntegralMixedChronologicalFrameCode.labels D) g.val.val g.val.val:=
    IntegralMixedChronologicalFrameCode.data_code D g.val g.val g.property g.property
  rw [block_codes_anchor,List.reverse_append,List.reverse_singleton,HA,
    IntegralMixedChronologicalCompanionCode.codes_actual]

theorem midpoint_block_codes {d birth :ℕ} (D :Descriptor d birth) (hk :D.labels.length<d+1)
    (a b :Fin birth) (g :Free (IntegralMixedChronologicalMidpoint.frame D hk a b).frozen):
    (IntegralMixedPointCompanion.codes (IntegralMixedChronologicalMidpoint.frame D hk a b).frozen
      (midpointDouble (IntegralMixedChronologicalMidpoint.next D hk))
      (IntegralMixedChronologicalMidpoint.rows D hk a b) g
      (IntegralMixedChronologicalMidpointSignature.orderedFree D hk a b++[g])).reverse=
      [IntegralMixedChronologicalMidpointCode.code d (IntegralMixedChronologicalFrameCode.labels D)
        a.val b.val g.val.val g.val.val]++
      IntegralMixedChronologicalMidpointCompanionCode.codes d (IntegralMixedChronologicalFrameCode.labels D)
        a.val b.val g.val.val:=by
  have HA :(pointData (IntegralMixedChronologicalMidpoint.frame D hk a b).frozen
      (midpointDouble (IntegralMixedChronologicalMidpoint.next D hk))
      (IntegralMixedChronologicalMidpoint.rows D hk a b) g 0 g).code=
      IntegralMixedChronologicalMidpointCode.code d (IntegralMixedChronologicalFrameCode.labels D)
        a.val b.val g.val.val g.val.val:=
    IntegralMixedChronologicalMidpointCode.data_code D hk a b g.val g.val g.property g.property
  rw [block_codes_anchor,List.reverse_append,List.reverse_singleton,HA,
    IntegralMixedChronologicalMidpointCompanionCode.codes_actual]

theorem exists_atomic_block {d S B birth :ℕ} {V :SpatialSource d} {ι :Type} [Fintype ι]
    (x :State V S B birth ι) (D :Descriptor d birth) (g :Free D.frame.frozen) (hn :0<d)
    (charge :ℕ) (hdegree :V.degree=BoundedZeroSource.powerDegree charge)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (d+1) V.degree≤2^B)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=
      z (x.sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) birth i)
    (old :Fin birth→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=old i)
    (p :Fin (d+1)→ℝ) (hp :p∈slice V D.frame old)
    (hg :∀i,i∉D.frame.frozen→i≠g.val→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial V.low V.leading V.degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (room :birth+(D.orderedFree++[g]).length≤S+1):
    Nonempty (Realized x D.frame.frozen (fun _=>false) (fun i=>.single (D.atom i)) g z φ old p
      (D.orderedFree++[g]) room):=
  (exists_realized x D.frame.frozen (fun _=>false) (fun i=>.single (D.atom i)) g hn charge hdegree hcap
    D.prefix_frozen z hz φ hφ old H p hp hg _ room).1

theorem exists_midpoint_block {d S B birth :ℕ} {V :SpatialSource d} {ι :Type} [Fintype ι]
    (x :State V S B birth ι) (D :Descriptor d birth) (hk :D.labels.length<d+1) (a b :Fin birth)
    (g :Free (IntegralMixedChronologicalMidpoint.frame D hk a b).frozen) (hn :0<d)
    (charge :ℕ) (hdegree :V.degree=BoundedZeroSource.powerDegree charge)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (d+1) V.degree≤2^B)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=
      z (x.sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) birth i)
    (old :Fin birth→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=old i)
    (p :Fin (d+1)→ℝ) (hp :p∈slice V D.frame old)
    (hmean :p (IntegralMixedChronologicalMidpoint.next D hk)=
      (old (IntegralMixedChronologicalMidpoint.reference a)+old (IntegralMixedChronologicalMidpoint.reference b))/2)
    (hg :∀i,i∉(IntegralMixedChronologicalMidpoint.frame D hk a b).frozen→i≠g.val→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial V.low V.leading V.degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (room :birth+(IntegralMixedChronologicalMidpointSignature.orderedFree D hk a b++[g]).length≤S+1):
    Nonempty (Realized x (IntegralMixedChronologicalMidpoint.frame D hk a b).frozen
      (midpointDouble (IntegralMixedChronologicalMidpoint.next D hk))
      (IntegralMixedChronologicalMidpoint.rows D hk a b) g z φ old p
      (IntegralMixedChronologicalMidpointSignature.orderedFree D hk a b++[g]) room):=by
  have HS :p∈slice V (IntegralMixedChronologicalMidpoint.frame D hk a b) old:=by
    rw [IntegralMixedChronologicalMidpoint.slice_eq]
    exact ⟨hp,hmean⟩
  exact (exists_realized x _ _ _ g hn charge hdegree hcap
    (IntegralMixedChronologicalMidpoint.prefix_frozen D hk a b) z hz φ hφ old H p HS hg _ room).1

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)

theorem prepared_number (old :List Bool) (e :ℕ):
    number n (preparedRoot hn ht ha hR0 old e)=n (IntegralMixedRoadmapAtomic.original old):=by
  simp only [number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,preparedRoot,IntegralMixedRoadmapAtomic.root,
    candidate_packet,pairFst_pair,IntegralMixedRoadmapAtomic.original]

theorem prepared_dimension (old :List Bool) (e :ℕ):
    (P).ambient (preparedRoot hn ht ha hR0 old e)=IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old:=by
  change number n (preparedRoot hn ht ha hR0 old e)+3=_
  rw [prepared_number,IntegralMixedRoadmapAtomic.dimension_eq]

theorem parent_length (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (e :ℕ) (he :e<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    (parentCommands hn ht ha hR0 old hv hd e he).length=
      IntegralMixedRoadmapAtomic.endBirth (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
        (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old:=by
  rw [parentCommands,IntegralMixedMarkedRecordContinuation.oldCommands_length,prepared_number]
  rw [IntegralMixedRoadmapAtomic.endBirth,IntegralMixedRoadmapAtomic.initial_eq]
  rfl

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedExceptionalBounds.auxiliaryCap
  preparedRoot start parentCommands parentState parentTuple
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  IntegralMixedRoadmapAtomic.endBirth IntegralMixedRoadmapAtomic.frozen

theorem parent_frame_good (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (e :ℕ) (he :e<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    IntegralMixedChronologicalFrameCode.Good ((P).ambient (preparedRoot hn ht ha hR0 old e))
      (parentCommands hn ht ha hR0 old hv hd e he).length (IntegralMixedRoadmapAtomic.frozen old):=by
  rw [parent_length,prepared_dimension]
  exact IntegralMixedRoadmapLevel.frame_mono (IntegralMixedRoadmapAtomic.own_frame_good hn ht ha hR0 old hv)
    (Nat.sub_le _ _)

noncomputable def parentDescriptor (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (e :ℕ) (he :e<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):=
  IntegralMixedChronologicalFrameCode.descriptor ((P).ambient (preparedRoot hn ht ha hR0 old e))
    (parentCommands hn ht ha hR0 old hv hd e he).length (IntegralMixedRoadmapAtomic.frozen old)
    (parent_frame_good hn ht ha hR0 old hv hd e he)

theorem parent_labels (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (e :ℕ) (he :e<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    IntegralMixedChronologicalFrameCode.labels (parentDescriptor hn ht ha hR0 old hv hd e he)=
    IntegralMixedRoadmapAtomic.frozen old:=by
  have HG :IntegralMixedChronologicalFrameCode.Good ((P).ambient (preparedRoot hn ht ha hR0 old e))
      (parentCommands hn ht ha hR0 old hv hd e he).length
      (IntegralMixedRoadmapChain.frozen (IntegralMixedRoadmapAtomic.payload old) (IntegralMixedRoadmapAtomic.depth old)):=by
    simpa only [IntegralMixedRoadmapAtomic.frozen] using parent_frame_good hn ht ha hR0 old hv hd e he
  simpa only [parentDescriptor,IntegralMixedRoadmapAtomic.frozen] using
    descriptor_frozen_labels _ _ _ _ HG

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalReplayAttachment
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedFieldRetention
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendOwnPoint
public import LeanCanny.Geometry.BoundedMarkedComponents
/-! # The actual marked prelude and its canonical retained references -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapMarkedPrelude
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedOriginalRegularSource
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false

noncomputable def Replay (q :List Bool):Prop:=
  IntegralMixedRoadmapAtomic.fullQuery q∈IntegralMixedPhysicalReplayRelation.language hn ht ha (radius_binary hR0) false

noncomputable def language :Language:={q |Replay hn ht ha hR0 q}

theorem decider :SpaceDecider (language hn ht ha hR0):=
  (IntegralMixedPhysicalReplayRelation.decider hn ht ha (radius_binary hR0) false
    (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha (radius_binary hR0) false)).precompose
      IntegralMixedRoadmapAtomic.fullQuery IntegralMixedRoadmapAtomic.fullQuery_FP

theorem candidate_root (q :List Bool):pairFst (IntegralMixedRoadmapAtomic.root q)=IntegralMixedRoadmapAtomic.candidate q:=by
  simp only [IntegralMixedRoadmapAtomic.root,pairFst_pair]

theorem original_root (q :List Bool):original (IntegralMixedRoadmapAtomic.root q)=IntegralMixedRoadmapAtomic.original q:=by
  simp only [original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
    IntegralMixedRoadmapAtomic.root,IntegralMixedRoadmapAtomic.original,pairFst_pair]

theorem number_root (q :List Bool):number n (IntegralMixedRoadmapAtomic.root q)=n (IntegralMixedRoadmapAtomic.original q):=
  congrArg n (original_root q)

noncomputable def value (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (i :ℕ):ℝ:=
  IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context q)
    (IntegralMixedRoadmapAtomic.word q) (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) i

/-- Coordinates of the actual marked prelude, with its LITERAL native source
ambient. It is independent of the later critical anchor's component. -/
noncomputable def point (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q):
    Fin (number n (IntegralMixedRoadmapAtomic.root q)+4)→ℝ:=fun i=>value hn ht ha hR0 q hv i.val

theorem full_valid (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q):
    SquareSampleCompleteVertices.Valid S
      (IntegralMixedPhysicalMarkedTest.sampleContext (IntegralMixedRoadmapAtomic.root q))
      (IntegralMixedRoadmapAtomic.word q):=
  IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedMarkedReservedParent.bank IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedRoadmapAtomic.depth IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapChain.entry
  IntegralMixedRoadmapChain.frozen IntegralMixedPhysicalFieldEquality.point value

theorem point_eq_native (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q):
    point hn ht ha hR0 q hv=IntegralMixedPhysicalMarkedSemantics.point hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.root q) (IntegralMixedRoadmapAtomic.word q) (full_valid hn ht ha hR0 q hv):=by
  funext i
  unfold point value IntegralMixedPhysicalMarkedSemantics.point
  have HI:=i.isLt
  exact (IntegralMixedPhysicalMarkedRetention.env_field hn ht ha hR0
    (IntegralMixedRoadmapAtomic.root q) (IntegralMixedRoadmapAtomic.word q) (full_valid hn ht ha hR0 q hv)
    i.val (by omega)).symm

/-- Native Replay binds this marked prelude to the supplied original candidate.
Neither the critical anchor nor a canonical slack phase is identified with it. -/
theorem exists_marked (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hr :Replay hn ht ha hR0 q):
    ∃hp :IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pairFst (IntegralMixedRoadmapAtomic.root q)),
    ∃z :BoundedRegularSource.Marked ((t (original (IntegralMixedRoadmapAtomic.root q))).finitePolynomial
        (number n (IntegralMixedRoadmapAtomic.root q)))
      (IntegralMixedMarkedPointTest.charge t (IntegralMixedRoadmapAtomic.root q))
      (IntegralMixedMarkedPointTest.charge t (IntegralMixedRoadmapAtomic.root q))
      (radius R0 (IntegralMixedRoadmapAtomic.root q)),
      z.val.val=point hn ht ha hR0 q hv ∧
      (BoundedRegularSource.markedProjection _ _ _ _ z).val=
        IntegralMixedAuxiliaryCandidate.point hn ht ha (pairFst (IntegralMixedRoadmapAtomic.root q)) hp:=by
  obtain ⟨hp,hw,z,HZ,HP⟩:=IntegralMixedPhysicalReplayAttachment.exists_point hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.root q) (IntegralMixedRoadmapAtomic.word q) hr
  exact ⟨hp,z,HZ.trans (point_eq_native hn ht ha hR0 q hv).symm,HP⟩

theorem point_source_zero (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hr :Replay hn ht ha hR0 q):
    (FermatCriticalHomogenization.polynomial
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (IntegralMixedRoadmapAtomic.root q)).low
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (IntegralMixedRoadmapAtomic.root q)).leading
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (IntegralMixedRoadmapAtomic.root q)).degree).eval₂
      (Int.castRingHom ℝ) (point hn ht ha hR0 q hv)=0:=by
  obtain ⟨_,z,HZ,_⟩:=exists_marked hn ht ha hR0 q hv hr
  rw [←HZ,IntegralMixedOriginalRegularSource.spatial_polynomial]
  exact z.val.property

/-- Every coordinate producer precedes the canonical parent. The five extra
prelude producers are not geometric coordinates. -/
theorem coordinate_before_parent (q :List Bool) (i :ℕ)
    (hi :i≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q):
    i<IntegralMixedRoadmapRetainedAppend.beginBirth hn ht ha hR0 q:=by
  have HD:=IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0 q
  have HN:=IntegralMixedRoadmapAtomic.initial_eq hn ht ha hR0 q
  unfold IntegralMixedRoadmapRetainedAppend.beginBirth IntegralMixedRoadmapAtomic.endBirth
  omega

theorem point_dimension (q :List Bool):
    number n (IntegralMixedRoadmapAtomic.root q)+4=
      IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q+1:=by
  rw [number_root,IntegralMixedRoadmapAtomic.dimension_eq]

/-- Producer i is retained bank reference m-1-i in the canonical parent. -/
noncomputable def parentIndex (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd :IntegralMixedRoadmapAtomic.depth q<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
    (e :ℕ) (he :e<IntegralMixedRoadmapRetainedAppend.beginBirth hn ht ha hR0 q)
    (i :ℕ) (hi :i≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q):
    Fin (IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 q hv hd e he).length:=
  ⟨(IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 q hv hd e he).length-1-i,by
    have HI:=coordinate_before_parent hn ht ha hR0 q i hi
    have HL:=IntegralMixedRoadmapRetainedAppend.parent_length hn ht ha hR0 q hv hd e he
    change _=IntegralMixedRoadmapRetainedAppend.beginBirth hn ht ha hR0 q at HL
    omega⟩

theorem canonical_value (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd :IntegralMixedRoadmapAtomic.depth q<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
    (e :ℕ) (he :e<IntegralMixedRoadmapRetainedAppend.beginBirth hn ht ha hR0 q)
    (i :ℕ) (hi :i≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q):
    IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 q hv hd e he
      (parentIndex hn ht ha hR0 q hv hd e he i hi)=value hn ht ha hR0 q hv i:=by
  rw [IntegralMixedRoadmapRetainedAppend.parent_value_old_field]
  have HI:=coordinate_before_parent hn ht ha hR0 q i hi
  have HL:=IntegralMixedRoadmapRetainedAppend.parent_length hn ht ha hR0 q hv hd e he
  change _=IntegralMixedRoadmapRetainedAppend.beginBirth hn ht ha hR0 q at HL
  have HR:(IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 q hv hd e he).length-1-
      (parentIndex hn ht ha hR0 q hv hd e he i hi).val=i:=by
    unfold parentIndex
    dsimp only
    omega
  rw [HR]
  unfold value
  rfl

end LeanCanny.Encoding.IntegralMixedRoadmapMarkedPrelude

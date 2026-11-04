/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapGraphGeometry
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendOwnPoint

/-! # Actual canonical and child histories describe the same numeric fibers -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedFrozenFrame Set
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "e" old=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "r" old=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old (e old)
local notation "Q" old=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (r old)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapAtomic.levels
  IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentDescriptor
  IntegralMixedRoadmapRetainedAppend.parentValues IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentCommands

theorem canonical_ambient_eq (c old :List Bool) (hc :IntegralMixedRoadmapAtomic.candidate old=c) :
    (P).ambient (r old)=n (pairFst c)+3:=by
  rw [IntegralMixedRoadmapRetainedAppend.prepared_dimension,IntegralMixedRoadmapAtomic.dimension_eq]
  change n (pairFst (IntegralMixedRoadmapAtomic.candidate old))+3=n (pairFst c)+3
  rw [hc]

noncomputable def canonicalPointAt (c old :List Bool) (hc :IntegralMixedRoadmapAtomic.candidate old=c)
    (p :Fin ((P).ambient (r old)+1)→ℝ) :Fin (n (pairFst c)+3+1)→ℝ:=fun i=>
  p (Fin.cast (congrArg (·+1) (canonical_ambient_eq hn ht ha hR0 c old hc)).symm i)

theorem canonicalPointAt_ownPoint (c old :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) (hc :IntegralMixedRoadmapAtomic.candidate old=c) :
    canonicalPointAt hn ht ha hR0 c old hc (IntegralMixedRoadmapRetainedAppend.ownPoint hn ht ha hR0 old hv)=
      pointAt hn ht ha hR0 c old hv hc:=by
  unfold canonicalPointAt IntegralMixedRoadmapRetainedAppend.ownPoint pointAt
  funext i
  apply congrArg (IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv)
  exact Fin.ext rfl

private theorem zero_cast_iff {a b :ℕ} (V :SpatialSource a) (W :SpatialSource b)
    (HD :a=b) (HS :HEq V W) (p :Fin (a+1)→ℝ) :
    (FermatCriticalHomogenization.polynomial W.low W.leading W.degree).eval₂ (Int.castRingHom ℝ)
      (fun i=>p (Fin.cast (congrArg (·+1) HD).symm i))=0 ↔
    (FermatCriticalHomogenization.polynomial V.low V.leading V.degree).eval₂ (Int.castRingHom ℝ) p=0:=by
  cases HD
  cases eq_of_heq HS
  rfl

private theorem prefix_cast_iff {a b k :ℕ} (HD :a=b) (levels :ℕ→ℝ) (p :Fin (a+1)→ℝ) :
    (∀i :Fin (b+1),i.val<k→p (Fin.cast (congrArg (·+1) HD).symm i)=levels i.val) ↔
      ∀i :Fin (a+1),i.val<k→p i=levels i.val:=by
  cases HD
  rfl

private theorem canonical_source_eq (c old :List Bool) (hc :IntegralMixedRoadmapAtomic.candidate old=c) :
    HEq (Q old) (originalSource (n:=n) (t:=t) (R0:=R0) c):=by
  rw [IntegralMixedOriginalRegularSource.spatial_source]
  apply IntegralMixedOriginalRegularSource.source_congr
  simpa only [IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
    IntegralMixedRoadmapRetainedAppend.preparedRoot,IntegralMixedRoadmapAtomic.root,
    IntegralMixedRoadmapRetainedAppend.candidate_packet,pairFst_pair,IntegralMixedRoadmapAtomic.original] using
      congrArg pairFst hc

private theorem canonical_parent_slice_numeric (old :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (p :Fin ((P).ambient (r old)+1)→ℝ) :
    p∈slice (Q old)
      (IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd (e old)
        (IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old)).frame
      (IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd (e old)
        (IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old)) ↔
    (FermatCriticalHomogenization.polynomial (Q old).low (Q old).leading (Q old).degree).eval₂
      (Int.castRingHom ℝ) p=0 ∧∀i :Fin ((P).ambient (r old)+1),
        i.val<IntegralMixedRoadmapAtomic.depth old→p i=IntegralMixedRoadmapAtomic.levels hn ht ha hR0 old hv i.val:=by
  let desc:=IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd (e old)
    (IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old)
  have HL:=IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd (e old)
    (IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old)
  change desc.labels.length=IntegralMixedRoadmapAtomic.depth old at HL
  rw [desc.slice_iff]
  constructor
  · rintro ⟨HZ,HF⟩
    refine ⟨HZ,?_⟩
    intro i hi
    let j :Fin desc.labels.length:=⟨i.val,by omega⟩
    have HP:=HF j
    have HV:=IntegralMixedRoadmapRetainedAppend.parent_frozen_value hn ht ha hR0 old hv hd (e old)
      (IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old) j
    have HE :(⟨j.val,lt_of_lt_of_le j.isLt desc.length_le⟩ :Fin ((P).ambient (r old)+1))=i:=Fin.ext rfl
    rw [HE] at HP
    exact HP.trans HV
  · rintro ⟨HZ,HF⟩
    refine ⟨HZ,?_⟩
    intro i
    have HI :i.val<IntegralMixedRoadmapAtomic.depth old:=by have :=i.isLt;omega
    exact (HF ⟨i.val,lt_of_lt_of_le i.isLt desc.length_le⟩ HI).trans
      (IntegralMixedRoadmapRetainedAppend.parent_frozen_value hn ht ha hR0 old hv hd (e old)
        (IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old) i).symm

/-- The actual canonical descriptor and its own bank values define exactly
the original-source numeric frozen slice. -/
theorem canonical_slice_iff_original (c old :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (hc :IntegralMixedRoadmapAtomic.candidate old=c) (p :Fin ((P).ambient (r old)+1)→ℝ) :
    p∈slice (Q old)
      (IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd (e old)
        (IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old)).frame
      (IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd (e old)
        (IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old)) ↔
      canonicalPointAt hn ht ha hR0 c old hc p∈frozenSlice (n:=n) (t:=t) (R0:=R0) c
        (IntegralMixedRoadmapAtomic.depth old) (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 old hv):=by
  rw [canonical_parent_slice_numeric hn ht ha hR0 old hv hd p]
  exact and_congr
    (zero_cast_iff (Q old) (originalSource (n:=n) (t:=t) (R0:=R0) c)
      (canonical_ambient_eq hn ht ha hR0 c old hc) (canonical_source_eq hn ht ha hR0 c old hc) p).symm
    (prefix_cast_iff (canonical_ambient_eq hn ht ha hR0 c old hc)
      (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 old hv) p).symm

theorem canonicalPointAt_continuous (c old :List Bool) (hc :IntegralMixedRoadmapAtomic.candidate old=c) :
    Continuous (canonicalPointAt hn ht ha hR0 c old hc):=by
  unfold canonicalPointAt
  exact continuous_pi (fun i=>continuous_apply _)

private theorem cast_point_surjective {a b :ℕ} (HD :a=b) :
    Function.Surjective (fun p :Fin (a+1)→ℝ=>fun i :Fin (b+1)=>p (Fin.cast (congrArg (·+1) HD).symm i)):=by
  cases HD
  exact fun p=>⟨p,rfl⟩

theorem canonical_slice_image (c old :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (hc :IntegralMixedRoadmapAtomic.candidate old=c) :
    canonicalPointAt hn ht ha hR0 c old hc ''
      slice (Q old)
        (IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd (e old)
          (IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old)).frame
        (IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd (e old)
          (IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old))=
      frozenSlice (n:=n) (t:=t) (R0:=R0) c (IntegralMixedRoadmapAtomic.depth old)
        (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 old hv):=by
  ext y
  constructor
  · rintro ⟨p,HP,rfl⟩
    exact (canonical_slice_iff_original hn ht ha hR0 c old hv hd hc p).mp HP
  · intro HY
    obtain ⟨p,HE⟩:=cast_point_surjective (canonical_ambient_eq hn ht ha hR0 c old hc) y
    change canonicalPointAt hn ht ha hR0 c old hc p=y at HE
    rw [←HE] at HY
    exact ⟨p,(canonical_slice_iff_original hn ht ha hR0 c old hv hd hc p).mpr HY,HE⟩

private theorem cast_point_joined_iff {a b :ℕ} (HD :a=b) (S :Set (Fin (a+1)→ℝ))
    (p q :Fin (a+1)→ℝ) :
    JoinedIn ((fun z :Fin (a+1)→ℝ=>fun i :Fin (b+1)=>z (Fin.cast (congrArg (·+1) HD).symm i)) '' S)
      (fun i=>p (Fin.cast (congrArg (·+1) HD).symm i))
      (fun i=>q (Fin.cast (congrArg (·+1) HD).symm i)) ↔JoinedIn S p q:=by
  cases HD
  change JoinedIn (id '' S) p q ↔JoinedIn S p q
  rw [Set.image_id]

/-- Path transport is across the proved coordinate cast, without moving any
complete sampler word between the two roots. -/
theorem canonical_slice_joined_iff (c old :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (hc :IntegralMixedRoadmapAtomic.candidate old=c) (p q :Fin ((P).ambient (r old)+1)→ℝ) :
    JoinedIn (slice (Q old)
      (IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd (e old)
        (IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old)).frame
      (IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd (e old)
        (IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old))) p q ↔
      JoinedIn (frozenSlice (n:=n) (t:=t) (R0:=R0) c (IntegralMixedRoadmapAtomic.depth old)
        (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 old hv))
        (canonicalPointAt hn ht ha hR0 c old hc p) (canonicalPointAt hn ht ha hR0 c old hc q):=by
  rw [←canonical_slice_image hn ht ha hR0 c old hv hd hc]
  exact (cast_point_joined_iff (canonical_ambient_eq hn ht ha hR0 c old hc) _ p q).symm

/-- The current height coordinate is bounded by the accepted parent's occurrence. -/
noncomputable def childCoordinate (c parent :List Bool)
    (hb :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 parent)
    (hc :IntegralMixedRoadmapAtomic.candidate parent=c) :Fin (n (pairFst c)+3+1):=
  ⟨IntegralMixedRoadmapAtomic.depth parent,by
    have HD:=(pointAt_occurrence hn ht ha hR0 c parent hb hc).depth_le
    change IntegralMixedRoadmapAtomic.depth parent≤n (pairFst c)+3 at HD
    omega⟩

theorem childCoordinate_val (c parent :List Bool)
    (hb :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 parent)
    (hc :IntegralMixedRoadmapAtomic.candidate parent=c) :
    (childCoordinate hn ht ha hR0 c parent hb hc).val=IntegralMixedRoadmapAtomic.depth parent:=rfl

/-- An accepted child's own numeric levels describe the old slice intersected
with its actual height fiber. No producer or sampler identification is assumed. -/
theorem child_frozenSlice_eq (c parent child :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 parent)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 child)
    (hc :IntegralMixedRoadmapAtomic.candidate parent=c) (hd :IntegralMixedRoadmapAtomic.candidate child=c)
    (hs :IntegralMixedRoadmapAtomic.depth child=IntegralMixedRoadmapAtomic.depth parent+1)
    (HF :pointAt hn ht ha hR0 c child hB hd∈frozenSlice (n:=n) (t:=t) (R0:=R0) c
      (IntegralMixedRoadmapAtomic.depth parent) (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 parent hA))
    (height :ℝ)
    (HH :pointAt hn ht ha hR0 c child hB hd (childCoordinate hn ht ha hR0 c parent hA hc)=height) :
    frozenSlice (n:=n) (t:=t) (R0:=R0) c (IntegralMixedRoadmapAtomic.depth child)
      (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 child hB)=
        frozenSlice (n:=n) (t:=t) (R0:=R0) c (IntegralMixedRoadmapAtomic.depth parent)
          (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 parent hA)∩
            {y |y (childCoordinate hn ht ha hR0 c parent hA hc)=height}:=by
  let coord:=childCoordinate hn ht ha hR0 c parent hA hc
  have HVal :coord.val=IntegralMixedRoadmapAtomic.depth parent:=rfl
  have HO:=pointAt_occurrence hn ht ha hR0 c child hB hd
  have HL (i :Fin (n (pairFst c)+3+1)) (hi :i.val<IntegralMixedRoadmapAtomic.depth parent) :
      IntegralMixedRoadmapAtomic.levels hn ht ha hR0 child hB i.val=
        IntegralMixedRoadmapAtomic.levels hn ht ha hR0 parent hA i.val:=
    (HO.frozen i (by omega)).symm.trans (HF.2 i hi)
  have HG :IntegralMixedRoadmapAtomic.levels hn ht ha hR0 child hB coord.val=height:=
    (HO.frozen coord (by omega)).symm.trans HH
  ext y
  constructor
  · intro HY
    refine ⟨⟨HY.1,fun i hi=>(HY.2 i (by omega)).trans (HL i hi)⟩,?_⟩
    exact (HY.2 coord (by omega)).trans HG
  · rintro ⟨HY,HT⟩
    refine ⟨HY.1,?_⟩
    intro i hi
    by_cases HI :i.val<IntegralMixedRoadmapAtomic.depth parent
    · exact (HY.2 i HI).trans (HL i HI).symm
    · have HE :i=coord:=Fin.ext (by omega)
      subst i
      exact HT.trans HG.symm

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapProperBranchReachability
public import LeanCanny.Connectivity.IntegralMixedRoadmapTerminalFiber
public import LeanCanny.Encoding.IntegralMixedRoadmapEqualAppendGeometry
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendGeometry
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendSampledExtension
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendMidSignature
/-! # Child-fiber recursion uses fresh accepted representatives -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Connectivity LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedRelativeCuts
open IntegralMixedFrozenFrame IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedFramedPhysicalIndex (arity enumerate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "E"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old E
local notation "cs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd E he
local notation "ho"=>IntegralMixedRoadmapRetainedAppend.parent_room hn ht ha hR0 old hv hd E he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd E he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd E he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd E he
local notation "z"=>IntegralMixedRoadmapRetainedAppend.parentTuple hn ht ha hR0 old hv hd E he
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd E he
local notation "Q"=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c
local notation "hQ"=>IntegralMixedStaticRecordPrefix.cap Q (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c)
local notation "phi"=>IntegralMixedRoadmapProperParent.hom hn ht ha hR0 old hv hd
local notation "hm"=>Nat.le_of_succ_le (IntegralMixedRoadmapProperParent.parent_room hn ht ha hR0 old hv hd)
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
local notation "h"=>IntegralMixedChronologicalSweepFrame.next d hk
local notation "choices"=>IntegralMixedRoadmapProperParent.choices hn ht ha hR0 old hv hd
noncomputable local instance fiberInductionIndexFintype :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapChain.metadata IntegralMixedRoadmapChain.rawStart
  IntegralMixedRoadmapRetainedAppend.start IntegralMixedRoadmapChain.depth
  IntegralMixedRoadmapChain.prefixCount IntegralMixedRoadmapChain.entry IntegralMixedRoadmapChain.frozen
  IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapRetainedAppend.parentTuple
  IntegralMixedRoadmapRetainedAppend.parentValues IntegralMixedExceptionalBounds.auxiliaryCap
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedFramedRawHeight.rootCeiling
  IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedFramedHistoryScript.run IntegralMixedHistory.reframe
  IntegralMixedFramedHistoryFamilyBits.initial IntegralMixedRoadmapProperParent.hom
  IntegralMixedRoadmapProperParent.choices IntegralMixedRoadmapRetainedAppend.parentState

/-- The recursive statement concerns the actual original-source slice and
actual native paths, allowing unrelated full words at its endpoints. -/
noncomputable def DepthComplete (candidate :List Bool) (k :ℕ) :Prop:=
  ∀a b, ∀(hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a),
    ∀(hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b),
    ∀(hc :IntegralMixedRoadmapAtomic.candidate a=candidate),
    ∀(hdc :IntegralMixedRoadmapAtomic.candidate b=candidate),
    IntegralMixedRoadmapAtomic.depth a=k→IntegralMixedRoadmapAtomic.depth b=k→
    JoinedIn (IntegralMixedRoadmapGraph.frozenSlice (n:=n) (t:=t) (R0:=R0) candidate
      (IntegralMixedRoadmapAtomic.depth a) (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 a hA))
      (IntegralMixedRoadmapGraph.pointAt hn ht ha hR0 candidate a hA hc)
      (IntegralMixedRoadmapGraph.pointAt hn ht ha hR0 candidate b hB hdc)→
        IntegralMixedRoadmapGraph.RawReachable hn ht ha hR0 candidate a b

theorem depth_complete_terminal (candidate :List Bool) :
    DepthComplete hn ht ha hR0 candidate (n (pairFst candidate)+3):=by
  intro first second hFirst hSecond hcFirst hcSecond hDepthFirst _ hPath
  have HP :JoinedIn (IntegralMixedRoadmapGraph.frozenSlice (n:=n) (t:=t) (R0:=R0) candidate
      (n (pairFst candidate)+3) (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 first hFirst))
      (IntegralMixedRoadmapGraph.pointAt hn ht ha hR0 candidate first hFirst hcFirst)
      (IntegralMixedRoadmapGraph.pointAt hn ht ha hR0 candidate second hSecond hcSecond):=by
    simpa only [hDepthFirst] using hPath
  exact (IntegralMixedRoadmapGraph.terminal_fiber_glue hn ht ha hR0 candidate first second
    hFirst hSecond hcFirst hcSecond hDepthFirst HP).2

open IntegralMixedRoadmapGraph

/-- The induction hypothesis at the next depth simulates a genuine boundary
fiber path. Both native representatives are constructed inside this proof. -/
theorem point_reachable_of_endpoint_fiber (endpoint :ParentEndpoint hn ht ha hR0 old hv hd)
    (HAllowed :endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (p q :Fin ((P).ambient c+1)→ℝ)
    (HP :p∈slice Q (d).frame V) (HQ :q∈slice Q (d).frame V)
    (Hph :p h=(endpoint.value V)) (Hqh :q h=(endpoint.value V))
    (HGp :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (HGq :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) q=0)
    (HJ :JoinedIn (slice Q (d).frame V∩{y |y h=(endpoint.value V)}) p q)
    (IH :DepthComplete hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
      (IntegralMixedRoadmapAtomic.depth old+1)) :
    PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
      (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl p)
      (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl q):=by
  have HA :endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices):=HAllowed
  obtain ⟨Rp,HEp⟩:=exists_equal_accepted_level hn ht ha hR0 old hv hd endpoint endpoint HA HA rfl p HP Hph HGp
  obtain ⟨Rq,HEq⟩:=exists_equal_accepted_level hn ht ha hR0 old hv hd endpoint endpoint HA HA rfl q HQ Hqh HGq
  obtain ⟨wp,hVp,hPp,_⟩:=HEp false
  obtain ⟨wq,hVq,hPq,_⟩:=HEq false
  let qp:=packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old Rp.leftSpec Rp.rightSpec false wp
  let qq:=packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old Rq.leftSpec Rq.rightSpec false wq
  have hcp :IntegralMixedRoadmapAtomic.candidate qp=IntegralMixedRoadmapAtomic.candidate old:=candidate_packet _ _ _ _ _ _
  have hcq :IntegralMixedRoadmapAtomic.candidate qq=IntegralMixedRoadmapAtomic.candidate old:=candidate_packet _ _ _ _ _ _
  have hdp :IntegralMixedRoadmapAtomic.depth qp=IntegralMixedRoadmapAtomic.depth old+1:=depth_packet _ _ _ _ _ _
  have hdq :IntegralMixedRoadmapAtomic.depth qq=IntegralMixedRoadmapAtomic.depth old+1:=depth_packet _ _ _ _ _ _
  have HPointp:=pointAt_eq_canonical_of_point_heq hn ht ha hR0 old qp hVp hcp p hPp
  have HPointq:=pointAt_eq_canonical_of_point_heq hn ht ha hR0 old qq hVq hcq q hPq
  let coord:=childCoordinate hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old hv rfl
  have Hcoord :Fin.cast (congrArg (·+1)
      (canonical_ambient_eq hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl)).symm coord=h:=by
    apply Fin.ext
    simp only [Fin.val_cast,coord,childCoordinate_val]
    exact (IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd E he).symm
  have HOld :pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) qp hVp hcp∈
      frozenSlice (n:=n) (t:=t) (R0:=R0) (IntegralMixedRoadmapAtomic.candidate old)
        (IntegralMixedRoadmapAtomic.depth old) (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 old hv):=by
    rw [HPointp]
    exact (canonical_slice_iff_original hn ht ha hR0 _ old hv hd rfl p).mp HP
  have Hheight :pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) qp hVp hcp coord=(endpoint.value V):=by
    rw [HPointp]
    change p (Fin.cast _ coord)=(endpoint.value V)
    rw [Hcoord]
    exact Hph
  have HSlice:=child_frozenSlice_eq hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old qp hv hVp
    rfl hcp hdp HOld (endpoint.value V) Hheight
  have HNative :JoinedIn
      (frozenSlice (n:=n) (t:=t) (R0:=R0) (IntegralMixedRoadmapAtomic.candidate old)
        (IntegralMixedRoadmapAtomic.depth qp) (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 qp hVp))
      (pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) qp hVp hcp)
      (pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) qq hVq hcq):=by
    rw [HPointp,HPointq,HSlice]
    apply (HJ.map (canonicalPointAt_continuous hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl).continuousOn).mono
    rintro y ⟨sample,hSample,rfl⟩
    refine ⟨(canonical_slice_iff_original hn ht ha hR0 _ old hv hd rfl sample).mp hSample.1,?_⟩
    change sample (Fin.cast _ coord)=(endpoint.value V)
    rw [Hcoord]
    exact hSample.2
  have HR:=IH qp qq hVp hVq hcp hcq hdp hdq HNative
  rw [←HPointp,←HPointq]
  exact point_reachable_of_raw hn ht ha hR0 hVp hVq hcp hcq HR


theorem point_reachable_of_child_fiber (height :ℝ)
    (HAllowed :height∈jointEndpointSet x hm phi (d).frame h g hg V choices)
    (p q :Fin ((P).ambient c+1)→ℝ)
    (HP :p∈slice Q (d).frame V) (HQ :q∈slice Q (d).frame V)
    (Hph :p h=height) (Hqh :q h=height)
    (HGp :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (HGq :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) q=0)
    (HJ :JoinedIn (slice Q (d).frame V∩{y |y h=height}) p q)
    (IH :DepthComplete hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
      (IntegralMixedRoadmapAtomic.depth old+1)) :
    PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
      (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl p)
      (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl q):=by
  exact point_reachable_of_endpoint_fiber hn ht ha hR0 old hv hd (.fresh height) HAllowed p q HP HQ Hph Hqh HGp HGq HJ IH

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapMatchedSlabSimulation
public import LeanCanny.Connectivity.IntegralMixedRoadmapCanonicalRetainedSweep
public import LeanCanny.Geometry.IntegralMixedMatchedFiniteSweep
public import LeanCanny.Geometry.IntegralMixedMatchedSlabAtomicPaths
/-! # Native simulation includes artificial empty-cut slabs -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Connectivity LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedRelativeCuts
open IntegralMixedFrozenFrame IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedFramedPhysicalIndex (arity enumerate)
open Set
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
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd E he
local notation "Q"=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c
local notation "hQ"=>IntegralMixedStaticRecordPrefix.cap Q (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c)
local notation "phi"=>IntegralMixedRoadmapProperParent.hom hn ht ha hR0 old hv hd
local notation "hm"=>Nat.le_of_succ_le (IntegralMixedRoadmapProperParent.parent_room hn ht ha hR0 old hv hd)
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
local notation "h"=>IntegralMixedChronologicalSweepFrame.next d hk
local notation "choices"=>IntegralMixedRoadmapProperParent.choices hn ht ha hR0 old hv hd
noncomputable local instance retainedSweepSlabSimulationIndexFintype :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs
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

open IntegralMixedRoadmapGraph

private theorem endpoint_reach_of_empty_branches {X J :Type*} [TopologicalSpace X] [IsEmpty J]
    {f :X→ℝ} {a b :ℝ} (D :ComponentSlabCover.InteriorData f a b J)
    (hab :a<b) {u v :X} (hu :f u=a∨f u=b) (H :D.EndpointReach u v):D.FiberLink u v:=by
  induction H with
  | refl=>exact D.fiberLink_refl hu
  | @tail y z _ HStep IH=>
    apply D.fiberLink_trans hab IH
    cases HStep with
    | left H=>exact Or.inl H
    | right H=>exact Or.inr H
    | forward j=>exact isEmptyElim j
    | backward j=>exact isEmptyElim j

private theorem sweep_subtype_fiber_path {X :Type*} [TopologicalSpace X] (K :Set X)
    (f :K→ℝ) (height :X→ℝ) (HF :∀y,f y=height y.val)
    (heightValue :ℝ) {u v :K} (H :JoinedIn (f ⁻¹' {heightValue}) u v):
    JoinedIn (K∩{y |height y=heightValue}) u.val v.val:=by
  apply (H.map continuous_subtype_val.continuousOn).mono
  rintro y ⟨w,hw,rfl⟩
  exact ⟨w.property,(HF w).symm.trans hw⟩

private theorem matched_slab_at_values
    (left right :ParentEndpoint hn ht ha hR0 old hv hd)
    (HL :left.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (HR :right.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (lo hi :ℝ) (HLeft :left.value V=lo) (HRight :right.value V=hi)
    (hab :lo<hi)
    (havoid :∀v,v∈Ioo lo hi→v∉IntegralMixedSelectedCriticalCuts.bad x hm
      (cutRule x (d).frame h g hg) phi choices)
    (hheight :Disjoint (Ioo lo hi) (realCriticalValues Q (line (d).frame h) V h))
    (M :MatchedSlabInterior x hm phi (line (d).frame h) h (Finset.mem_insert_self _ _) g hg V lo hi
      ⟨(lo+hi)/2,by constructor <;> linarith⟩)
    (p q :Fin ((P).ambient c+1)→ℝ)
    (HP :p∈slice Q (d).frame V) (HQ :q∈slice Q (d).frame V)
    (Hph :p h=lo∨p h=hi) (Hqh :q h=lo∨q h=hi)
    (HGp :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (HGq :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) q=0)
    (HJ :JoinedIn (slice Q (d).frame V∩{y |y h∈Icc lo hi}) p q)
    (IH :DepthComplete hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
      (IntegralMixedRoadmapAtomic.depth old+1)):
    PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
      (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl p)
      (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl q):=by
  subst lo
  subst hi
  exact point_reachable_of_matched_slab hn ht ha hR0 old hv hd left right HL HR hab havoid hheight
    M p q HP HQ Hph Hqh HGp HGq HJ IH

theorem point_reachable_of_retained_sweep_slab
    (targetRef :Fin (cs).length)
    (W :RetainedMatchedFiniteSweep x hm phi (d).frame h g hg V choices targetRef)
    (i :Fin (W.slabs+1))
    (p q :Fin ((P).ambient c+1)→ℝ)
    (HP :p∈slice Q (d).frame V) (HQ :q∈slice Q (d).frame V)
    (Hph :p h=W.cut i.val∨p h=W.cut (i.val+1))
    (Hqh :q h=W.cut i.val∨q h=W.cut (i.val+1))
    (HGp :∀j,j∉insert h (d).frame.frozen→j≠g→
      (MvPolynomial.pderiv j (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (HGq :∀j,j∉insert h (d).frame.frozen→j≠g→
      (MvPolynomial.pderiv j (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) q=0)
    (HJ :JoinedIn (slice Q (d).frame V∩{y |y h∈Icc (W.cut i.val) (W.cut (i.val+1))}) p q)
    (IH :DepthComplete hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
      (IntegralMixedRoadmapAtomic.depth old+1)):
    PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
      (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl p)
      (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl q):=by
  let a:=W.cut i.val
  let b:=W.cut (i.val+1)
  let M:=W.matched i
  have hab :a<b:=W.strict (Fin.castSucc_lt_succ (i:=i))
  have Hgap :∀v∈Ioo a b,v∉jointEndpointSet x hm phi (d).frame h g hg V choices:=W.gap i
  by_cases HBoth :(∃left :ParentEndpoint hn ht ha hR0 old hv hd,
      left.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices) ∧ left.value V=a) ∧
    (∃right :ParentEndpoint hn ht ha hR0 old hv hd,
      right.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices) ∧ right.value V=b)
  · obtain ⟨⟨left,HL,HLeft⟩,⟨right,HR,HRight⟩⟩:=HBoth
    exact matched_slab_at_values hn ht ha hR0 old hv hd left right HL HR a b HLeft HRight hab
      (fun v hv hbad=>Hgap v hv (Or.inl hbad))
      (Set.disjoint_left.mpr (fun v hv hbad=>Hgap v hv (Or.inr hbad))) M
      p q HP HQ Hph Hqh HGp HGq HJ IH
  have hh:=IntegralMixedChronologicalSweepFrame.next_free d hk
  let K:=slice Q (coarse (line (d).frame h) h) V
  let u :K:=⟨p,by simpa only [K,coarse_line (d).frame h hh] using HP⟩
  let v :K:=⟨q,by simpa only [K,coarse_line (d).frame h hh] using HQ⟩
  have HProjection (y :K):coarseProjection Q (line (d).frame h) V h y=y.val h:=
    line_projection (d).frame h ((d).free_normal h hh) V y.val
  have HUsed (j :Fin (W.slabs+2)) (y :K)
      (HY :coarseProjection Q (line (d).frame h) V h y=W.cut j.val):
      ∃endpoint :ParentEndpoint hn ht ha hR0 old hv hd,
        endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices) ∧ endpoint.value V=W.cut j.val:=by
    rcases W.origin j with Hbad|Hempty
    · exact Hbad
    · have HFiber :y∈(coarseProjection Q (line (d).frame h) V h) ⁻¹' {W.cut j.val}:=HY
      rw [Hempty] at HFiber
      exact False.elim HFiber
  let J:=IntegralMixedSelectedPhysicalFiber.physical (cutSource x (d).frame h) hm
    (cutRule x (d).frame h g hg) phi (consecutiveMidpoint W.cut W.strict i).val
  let :IsEmpty J:=⟨fun j=>HBoth ⟨HUsed i.castSucc (M.interior.arc j a) (M.interior.level_left j),
    HUsed i.succ (M.interior.arc j b) (M.interior.level_right j)⟩⟩
  let :=M.finite_index
  let :=W.finite_endpoint i.castSucc
  let :=W.finite_endpoint i.succ
  have HU :coarseProjection Q (line (d).frame h) V h u=a∨
      coarseProjection Q (line (d).frame h) V h u=b:=by rw [HProjection];exact Hph
  have HV :coarseProjection Q (line (d).frame h) V h v=a∨
      coarseProjection Q (line (d).frame h) V h v=b:=by rw [HProjection];exact Hqh
  have HUcc :u∈(coarseProjection Q (line (d).frame h) V h) ⁻¹' Icc a b:=by
    rcases HU with HE|HE <;> change _∈Icc a b <;> rw [HE] <;> exact ⟨by linarith,by linarith⟩
  have HVcc :v∈(coarseProjection Q (line (d).frame h) V h) ⁻¹' Icc a b:=by
    rcases HV with HE|HE <;> change _∈Icc a b <;> rw [HE] <;> exact ⟨by linarith,by linarith⟩
  have HSub :JoinedIn ((coarseProjection Q (line (d).frame h) V h) ⁻¹' Icc a b) u v:=by
    have HI:=Topology.IsEmbedding.subtypeVal.isInducing.joinedIn_image HUcc HVcc
    rw [closed_slab_image Q (d).frame V h hh (d).free_normal a b] at HI
    exact HI.mp HJ
  have HWalk:=(M.interior.endpoint_joined_iff_reach (W.endpointCover i.castSucc) (W.endpointCover i.succ)
    (coarseProjection_continuous Q (line (d).frame h) V h) hab
    (consecutiveMidpoint W.cut W.strict i) M.clopen HU HV).mp HSub
  have HFiber:=endpoint_reach_of_empty_branches (J:=J) M.interior hab HU HWalk
  have HReach (height :ℝ) (j :Fin (W.slabs+2)) (HC :W.cut j.val=height)
      (HF :JoinedIn ((coarseProjection Q (line (d).frame h) V h) ⁻¹' {height}) u v):
      PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
        (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl p)
        (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl q):=by
    obtain ⟨endpoint,HAllowed,HValue0⟩:=HUsed j u (HF.source_mem.trans HC.symm)
    have HValue :endpoint.value V=height:=HValue0.trans HC
    apply point_reachable_of_endpoint_fiber hn ht ha hR0 old hv hd endpoint HAllowed p q HP HQ
      (((HProjection u).symm.trans HF.source_mem).trans HValue.symm)
      (((HProjection v).symm.trans HF.target_mem).trans HValue.symm) HGp HGq
    · rw [HValue]
      simpa only [K,coarse_line (d).frame h hh] using
        sweep_subtype_fiber_path K _ (fun y=>y h) HProjection height HF
    · exact IH
  rcases HFiber with HF|HF
  · exact HReach a i.castSucc rfl HF
  · exact HReach b i.succ rfl HF

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

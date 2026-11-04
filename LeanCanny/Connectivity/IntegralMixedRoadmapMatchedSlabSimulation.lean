/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapFiberInduction
public import LeanCanny.Geometry.IntegralMixedMatchedSlabAtomicPaths
/-! # Native simulation of a genuine matched slab endpoint path -/
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
private theorem atomic_walk_simulation {X J :Type*} [TopologicalSpace X] {f :X→ℝ} {a b :ℝ}
    (D :ComponentSlabCover.InteriorData f a b J) (K :Set X) (R :X→X→Prop)
    (HTrans :∀{x y z},R x y→R y z→R x z)
    (HRefl :∀x∈K,R x x)
    (HStep :∀x∈K,∀y∈K,ComponentSlabCover.InteriorData.EndpointStep D x y→R x y)
    {x y :K} (H :D.AtomicEndpointReach K x y):R x.val y.val:=by
  induction H with
  | refl=>exact HRefl _ x.property
  | @tail y z _ h IH=>exact HTrans IH (HStep _ y.property _ z.property h)

private theorem subtype_fiber_path {X :Type*} [TopologicalSpace X] (S :Set X)
    (f :S→ℝ) (height :X→ℝ) (HF :∀y,f y=height y.val)
    (t :ℝ) {u v :S} (H :JoinedIn (f ⁻¹' {t}) u v):
    JoinedIn (S∩{y |height y=t}) u.val v.val:=by
  apply (H.map continuous_subtype_val.continuousOn).mono
  rintro y ⟨w,hw,rfl⟩
  exact ⟨w.property,(HF w).symm.trans hw⟩

private theorem branch_endpoint_data {a S B m :ℕ} {P :SpatialSource a} {ι :Type}
    (x :State P S B m ι) (hm :m≤S) (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F :Frame a) (h :Fin (a+1)) (hh :h∉F.frozen) (HF :FreeNormal F)
    (g :Fin (a+1)) (hg :g∉(line F h).frozen) (values :Fin m→ℝ)
    (HV :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (lo hi :ℝ) (center :Ioo lo hi)
    (M :MatchedSlabInterior x hm φ (line F h) h (Finset.mem_insert_self _ _) g hg values lo hi center)
    (j :IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ center.val)
    (t :ℝ) (ht :t∈Icc lo hi):
    (M.interior.arc j t).val∈slice P F values ∧ (M.interior.arc j t).val h=t ∧
      ∀i,i∉insert h F.frozen→i≠g→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
          (Int.castRingHom ℝ) (M.interior.arc j t).val=0:=by
  rw [M.readback j t ht]
  exact selected_point_endpoint x hm φ F h hh HF g hg values HV t _ (M.physical j t ht)

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
noncomputable local instance matchedSlabSimulationIndexFintype :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs
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
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
local notation "a"=>left.value V
local notation "b"=>right.value V

/-- A genuine closed-slab path between critical boundary points is simulated
by the actual native graph, using only the next-depth recursive statement. -/
theorem point_reachable_of_matched_slab
    (HL :left.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (HR :right.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (hab :a<b)
    (havoid :∀v,v∈Ioo a b→v∉IntegralMixedSelectedCriticalCuts.bad x hm
      (cutRule x (d).frame h g hg) phi choices)
    (hheight :Disjoint (Ioo a b) (realCriticalValues Q (line (d).frame h) V h))
    (M :MatchedSlabInterior x hm phi (line (d).frame h) h (Finset.mem_insert_self _ _) g hg V a b
      ⟨(a+b)/2,by constructor <;> linarith⟩)
    (p q :Fin ((P).ambient c+1)→ℝ)
    (HP :p∈slice Q (d).frame V) (HQ :q∈slice Q (d).frame V)
    (Hph :p h=a∨p h=b) (Hqh :q h=a∨q h=b)
    (HGp :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (HGq :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) q=0)
    (HJ :JoinedIn (slice Q (d).frame V∩{y |y h∈Icc a b}) p q)
    (IH :DepthComplete hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
      (IntegralMixedRoadmapAtomic.depth old+1)):
    PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
      (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl p)
      (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl q):=by
  have hh:=IntegralMixedChronologicalSweepFrame.next_free d hk
  have hfirst :(h).val=(d).frame.frozen.card:=(d).frozen_card.symm
  obtain ⟨R,_⟩:=IntegralMixedRoadmapProperParent.exists_guarded_pair hn ht ha hR0 old hv hd left right HL HR
  have HRoom :(cs).length+R.result.commands.length+((P).ambient c-(d).frame.frozen.card)≤(P).cap c+2:=by
    have HB:=canonical_level_horizon hn ht ha hR0 old hv hd
    have HC:=R.result.count
    rw [(d).frozen_card]
    omega
  have HProper :IsProperMap (fun y :Fin ((P).ambient c+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree).eval₂ (Int.castRingHom ℝ) y):=
    regular_source_proper (BoundedRegularLowCoefficient.readers (IntegralMixedAuxiliaryMarkedIntegerSource.number n)
      (t∘IntegralMixedAuxiliaryMarkedIntegerSource.original) (radius R0)) c
  let S:=slice Q (coarse (line (d).frame h) h) V
  let u :S:=⟨p,by simpa only [S,coarse_line (d).frame h hh] using HP⟩
  let v :S:=⟨q,by simpa only [S,coarse_line (d).frame h hh] using HQ⟩
  have HProjection (y :S):coarseProjection Q (line (d).frame h) V h y=y.val h:=
    line_projection (d).frame h ((d).free_normal h hh) V y.val
  have HU :coarseProjection Q (line (d).frame h) V h u=a∨
      coarseProjection Q (line (d).frame h) V h u=b:=by rw [HProjection];exact Hph
  have HV :coarseProjection Q (line (d).frame h) V h v=a∨
      coarseProjection Q (line (d).frame h) V h v=b:=by rw [HProjection];exact Hqh
  have HWalk:=(R.result.matched_atomic_paths hm h hh hfirst (d).free_normal g hg
    (t (IntegralMixedAuxiliaryMarkedIntegerSource.original c)).toData.size
    (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t (radius R0) c) HProper HRoom hab
    ⟨(a+b)/2,by constructor <;> linarith⟩ M u v HU HV).mp HJ
  let K:=M.interior.endpointSupport u v
  let Good (y :S):Prop:=(y.val h=a∨y.val h=b) ∧ ∀i,i∉insert h (d).frame.frozen→i≠g→
    (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
      (Int.castRingHom ℝ) y.val=0
  have HSupport :∀y∈K,Good y:=by
    intro y hy
    simp only [K,ComponentSlabCover.InteriorData.endpointSupport,mem_insert_iff,mem_union,mem_range] at hy
    rcases hy with rfl|rfl|⟨j,rfl⟩|⟨j,rfl⟩
    · exact ⟨Hph,HGp⟩
    · exact ⟨Hqh,HGq⟩
    · have H:=branch_endpoint_data x hm phi (d).frame h hh (d).free_normal g hg V
        (IntegralMixedRoadmapProperParent.hom_values hn ht ha hR0 old hv hd) a b _ M j a ⟨le_rfl,hab.le⟩
      exact ⟨Or.inl H.2.1,H.2.2⟩
    · have H:=branch_endpoint_data x hm phi (d).frame h hh (d).free_normal g hg V
        (IntegralMixedRoadmapProperParent.hom_values hn ht ha hR0 old hv hd) a b _ M j b ⟨hab.le,le_rfl⟩
      exact ⟨Or.inr H.2.1,H.2.2⟩
  let Reach (y z :S):Prop:=PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
    (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl y.val)
    (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl z.val)
  have HFiber (endpoint :ParentEndpoint hn ht ha hR0 old hv hd)
      (HA :endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
      (y z :S) (hy :y∈K) (hz :z∈K)
      (H :JoinedIn ((coarseProjection Q (line (d).frame h) V h) ⁻¹' {endpoint.value V}) y z):Reach y z:=by
    exact point_reachable_of_endpoint_fiber hn ht ha hR0 old hv hd endpoint HA y.val z.val
      (by simpa only [S,coarse_line (d).frame h hh] using y.property)
      (by simpa only [S,coarse_line (d).frame h hh] using z.property)
      ((HProjection y).symm.trans H.source_mem) ((HProjection z).symm.trans H.target_mem)
      (HSupport y hy).2 (HSupport z hz).2
      (by simpa only [S,coarse_line (d).frame h hh] using
        subtype_fiber_path S _ (fun p=>p h) HProjection (endpoint.value V) H) IH
  have HRefl (y :S) (hy :y∈K):Reach y y:=by
    rcases (HSupport y hy).1 with HE|HE
    · exact HFiber left HL y y hy hy (JoinedIn.refl ((HProjection y).trans HE))
    · exact HFiber right HR y y hy hy (JoinedIn.refl ((HProjection y).trans HE))
  have HStep (y :S) (hy :y∈K) (z :S) (hz :z∈K)
      (H :ComponentSlabCover.InteriorData.EndpointStep M.interior y z):Reach y z:=by
    cases H with
    | left H=>exact HFiber left HL _ _ hy hz H
    | right H=>exact HFiber right HR _ _ hy hz H
    | forward j=>
      have HR:=IntegralMixedRoadmapGraph.proper_branch_point_reachable hn ht ha hR0 old hv hd left right
        HL HR hab havoid hheight M j
      exact (congrArg₂ (fun p q=>PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
        (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl p)
        (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl q))
        (M.readback j a ⟨le_rfl,hab.le⟩) (M.readback j b ⟨hab.le,le_rfl⟩)).mpr HR
    | backward j=>
      have HR:=IntegralMixedRoadmapGraph.proper_branch_point_reachable hn ht ha hR0 old hv hd left right
        HL HR hab havoid hheight M j
      exact (congrArg₂ (fun p q=>PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
        (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl p)
        (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl q))
        (M.readback j b ⟨hab.le,le_rfl⟩) (M.readback j a ⟨le_rfl,hab.le⟩)).mpr HR.symm
  exact atomic_walk_simulation M.interior K Reach
    (fun H K=>IntegralMixedRoadmapGraph.PointReachable.trans hn ht ha hR0 H K) HRefl HStep HWalk

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

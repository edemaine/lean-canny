/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapFirstSeedComponent
public import LeanCanny.Encoding.IntegralMixedRoadmapFirstSeedAcceptance
/-! # Accepted first seeds retain the marked candidate's component incidence -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open Set LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.point
  IntegralMixedPhysicalPointCompanionScan.geometricPoint
  IntegralMixedRoadmapSeedResampling.preparedRoot IntegralMixedRoadmapSeedResampling.seedNativePoint

private theorem cast_point_heq' {a b :ℕ} (H :a=b) (p :Fin a→ℝ) :
    HEq p (fun i :Fin b=>p (Fin.cast H.symm i)):=by cases H;rfl

private theorem geometric_congr (c d w v :List Bool) (a b :ℕ)
    (hc :SquareSampleCompleteVertices.Valid S c w)
    (hd :SquareSampleCompleteVertices.Valid S d v)
    (he :c=d) (hw :w=v) (hb :a=b) :
    HEq (IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false c w hc a)
      (IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false d v hd b):=by
  subst d;subst v;subst b;rfl

private theorem atomic_point_congr (q r :List Bool) (hq :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hr :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 r) (he :q=r) :
    HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hq) (IntegralMixedRoadmapAtomic.point hn ht ha hR0 r hr):=by subst r;rfl

/-- Block zero is the accepted depth-zero anchor, on the same full word. -/
theorem first_seed_point_of_readback (old w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (IntegralMixedRoadmapSeedMetadata.context hn ht ha hR0 old) w)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w))
    (p :Fin ((P).ambient (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old)+1)→ℝ)
    (hr :IntegralMixedRoadmapSeedMetadata.Readback hn ht ha hR0 old w hw (IntegralMixedRoadmapSeedResampling.seedNativePoint hn ht ha hR0 old p)) :
    HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w) hv) p:=by
  let q:=IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w
  have HI :IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q=
      IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old)+8:=by
    rw [IntegralMixedRoadmapSeedResampling.initial_packet hn ht ha hR0,IntegralMixedRoadmapAtomic.initial]
    exact (IntegralMixedRoadmapSeedMetadata.initial_root hn ht ha hR0 old).symm
  have HAnchor :IntegralMixedRoadmapAtomic.anchor (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q=
      IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old)+8:=by
    rw [IntegralMixedRoadmapAtomic.seed_anchor _ _ q (IntegralMixedRoadmapSeedResampling.depth_packet _ _ _)]
    exact HI
  have HH:=geometric_congr hn ht ha hR0 (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapSeedMetadata.context hn ht ha hR0 old)
    (IntegralMixedRoadmapAtomic.word q) w (IntegralMixedRoadmapAtomic.anchor (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q)
    (IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old)+8)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) hw (IntegralMixedRoadmapSeedMetadata.packet_context hn ht ha hR0 old w)
    (IntegralMixedRoadmapSeedResampling.word_packet _ _ _) HAnchor
  change HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv) p
  have HH' :HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv)
      (IntegralMixedRoadmapSeedResampling.seedNativePoint hn ht ha hR0 old p):=by
    have HK:=IntegralMixedRoadmapSeedMetadata.seed_count_lower hn ht ha hR0 old
    have HR:=hr.physical 0 (by omega)
    simp only [Nat.add_zero] at HR
    simpa only [IntegralMixedRoadmapAtomic.point] using HH.trans (heq_of_eq HR)
  have HP :HEq (IntegralMixedRoadmapSeedResampling.seedNativePoint hn ht ha hR0 old p) p:=by
    unfold IntegralMixedRoadmapSeedResampling.seedNativePoint
    exact (cast_point_heq' (congrArg (·+1) (IntegralMixedRoadmapSeedResampling.seed_native_dimension hn ht ha hR0 old)).symm p).symm
  exact HH'.trans HP

private theorem critical_transport {a b :ℕ} (Q :SpatialSource a) (R :SpatialSource b)
    (hd :a=b) (hs :HEq Q R) (p :Fin (a+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg :∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂ (Int.castRingHom ℝ) p=0) :
    ∃r :Fin (b+1)→ℝ,HEq r p ∧
      (FermatCriticalHomogenization.polynomial R.low R.leading R.degree).eval₂ (Int.castRingHom ℝ) r=0 ∧
      ∀i,i.val≠0→(MvPolynomial.pderiv i
        (FermatCriticalHomogenization.polynomial R.low R.leading R.degree)).eval₂ (Int.castRingHom ℝ) r=0:=by
  cases hd
  have HE :Q=R:=eq_of_heq hs
  subst R
  exact ⟨p,HEq.rfl,hp,hg⟩

/-- A newly accepted first seed represents a point in the source component of
the canonical marked lift of this candidate. The heterogeneous equality only
accounts for native ambient-index casts; it compares the entire point. -/
theorem exists_first_seed_in_component (u label :List Bool)
    (hg :AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (hR :IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u) :
    ∃w,∃hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapAtomic.packet (pair u label) (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w),
      ∃p :Fin (n u+3+1)→ℝ,
        p∈connectedComponentIn (firstZeroSet (n:=n) (t:=t) (R0:=R0) u)
          (firstMarkedPoint hn ht ha u label hg hR) ∧
        HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 (IntegralMixedRoadmapAtomic.packet (pair u label) (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w) hv) p:=by
  obtain ⟨p,HP,HZ,HG⟩:=exists_original_component_critical hn ht ha u label hg hR
  let r:=IntegralMixedRoadmapFirstSeed.root hn ht ha hR0 u label
  let Q:=IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r
  have HO :IntegralMixedAuxiliaryMarkedIntegerSource.original r=u:=by
    simp only [r,IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedRoadmapFirstSeed.candidate_root,pairFst_pair]
  have HD :n u+3=IntegralMixedAuxiliaryMarkedIntegerSource.number n r+3:=by rw [IntegralMixedRoadmapFirstSeed.number_root]
  have HS :HEq (source n t R0 u) Q:=by
    change HEq (source n t R0 u) (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r)
    rw [IntegralMixedOriginalRegularSource.spatial_source]
    exact (IntegralMixedOriginalRegularSource.source_congr n t R0 _ _ HO).symm
  obtain ⟨pN,HE,HN,HC⟩:=critical_transport _ _ HD HS p HZ HG
  obtain ⟨w,hw,hv,HR⟩:=IntegralMixedRoadmapFirstSeed.exists_at hn ht ha hR0 u label hg hR pN HN HC
  have HPacket:=IntegralMixedRoadmapFirstSeed.packet_eq hn ht ha hR0 u label w
  have hv0 :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
      (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (IntegralMixedRoadmapFirstSeed.base u label)) (IntegralMixedRoadmapFirstSeed.base u label) w):=
    Eq.mpr (congrArg (IntegralMixedRoadmapAtomic.Valid hn ht ha hR0) HPacket) hv
  have HH:=first_seed_point_of_readback hn ht ha hR0 (IntegralMixedRoadmapFirstSeed.base u label) w hw hv0 pN HR
  have HH':=atomic_point_congr hn ht ha hR0 _ _ hv0 hv HPacket
  exact ⟨w,hv,p,HP,HH'.symm.trans (HH.trans HE)⟩

theorem firstSeed_candidate (u label w :List Bool) :
    IntegralMixedRoadmapAtomic.candidate (IntegralMixedRoadmapAtomic.packet (pair u label)
      (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w)=pair u label:=by
  simp only [IntegralMixedRoadmapAtomic.packet,IntegralMixedRoadmapAtomic.candidate,pairFst_pair]

/-- The actual graph point, with only the parser's original-index cast removed. -/
noncomputable def firstSeedPoint (u label w :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapAtomic.packet (pair u label)
      (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w)) :Fin (n u+3+1)→ℝ:=fun i=>
  pointAt hn ht ha hR0 (pair u label) (IntegralMixedRoadmapAtomic.packet (pair u label)
    (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w) hv (firstSeed_candidate u label w)
      (Fin.cast (congrArg (fun a :List Bool=>n a+3+1) (pairFst_pair u label)).symm i)

theorem firstSeedPoint_of_point_heq (u label w :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapAtomic.packet (pair u label)
      (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w))
    (p :Fin (n u+3+1)→ℝ)
    (hp :HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0
      (IntegralMixedRoadmapAtomic.packet (pair u label)
        (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w) hv) p) :
    firstSeedPoint hn ht ha hR0 u label w hv=p:=by
  let q:=IntegralMixedRoadmapAtomic.packet (pair u label)
    (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w
  have H0 :HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv)
      (pointAt hn ht ha hR0 (pair u label) q hv (firstSeed_candidate u label w)):=by
    unfold pointAt
    exact cast_point_heq' (congrArg (·+1) (ambient_eq hn ht ha hR0 (pair u label) q (firstSeed_candidate u label w))) _
  have H1 :HEq (pointAt hn ht ha hR0 (pair u label) q hv (firstSeed_candidate u label w))
      (firstSeedPoint hn ht ha hR0 u label w hv):=by
    unfold firstSeedPoint
    exact cast_point_heq' (congrArg (fun a :List Bool=>n a+3+1) (pairFst_pair u label)) _
  exact eq_of_heq ((H0.trans H1).symm.trans hp)

/-- No accepted old history is assumed: the new seed's actual graph point lies
in the component of the original candidate's canonical marked lift. -/
theorem exists_first_seed_incident (u label :List Bool)
    (hg :AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (hR :IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u) :
    ∃w,∃hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
      (IntegralMixedRoadmapAtomic.packet (pair u label)
        (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w),
      firstSeedPoint hn ht ha hR0 u label w hv∈
        connectedComponentIn (firstZeroSet (n:=n) (t:=t) (R0:=R0) u)
          (firstMarkedPoint hn ht ha u label hg hR):=by
  obtain ⟨w,hv,p,HP,HE⟩:=exists_first_seed_in_component hn ht ha hR0 u label hg hR
  refine ⟨w,hv,?_⟩
  rw [firstSeedPoint_of_point_heq hn ht ha hR0 u label w hv p HE]
  exact HP

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph

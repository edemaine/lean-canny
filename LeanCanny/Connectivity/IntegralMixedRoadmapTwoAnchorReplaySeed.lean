/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorOriginalPoints
public import LeanCanny.Encoding.IntegralMixedRoadmapFirstSeedReplay
public import LeanCanny.Connectivity.IntegralMixedRoadmapFirstSeedIncidence
/-! # A fresh Replay seed at one prescribed original global critical point -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorGeometry
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem critical_transport {a b :ℕ} (Q :IntegralMixedHistory.SpatialSource a)
    (R :IntegralMixedHistory.SpatialSource b) (hd :a=b) (hs :HEq Q R) (p :Fin (a+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg :∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂ (Int.castRingHom ℝ) p=0):
    ∃r :Fin (b+1)→ℝ,HEq r p ∧
      (FermatCriticalHomogenization.polynomial R.low R.leading R.degree).eval₂ (Int.castRingHom ℝ) r=0 ∧
      ∀i,i.val≠0→(MvPolynomial.pderiv i
        (FermatCriticalHomogenization.polynomial R.low R.leading R.degree)).eval₂ (Int.castRingHom ℝ) r=0:=by
  cases hd
  cases eq_of_heq hs
  exact ⟨p,HEq.rfl,hp,hg⟩
private theorem cast_point_heq {a b :ℕ} (H :a=b) (p :Fin a→ℝ):
    HEq p (fun i :Fin b=>p (Fin.cast H.symm i)):=by cases H;rfl

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapIdentity.point point
  IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.source IntegralMixedRoadmapAtomic.levels
  IntegralMixedRoadmapSeedResampling.preparedRoot IntegralMixedRoadmapSeedResampling.seedNativePoint

private theorem atomic_point_congr (a b :List Bool) (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b) (H :a=b):
    HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 a hA) (IntegralMixedRoadmapAtomic.point hn ht ha hR0 b hB):=by
  subst b;rfl

theorem exists_replay_at_original (u label :List Bool)
    (hg :AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (hR :IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u)
    (p :Fin (n u+4)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial (source n t R0 u).low
      (source n t R0 u).leading (source n t R0 u).degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hcrit :∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (source n t R0 u).low
        (source n t R0 u).leading (source n t R0 u).degree)).eval₂ (Int.castRingHom ℝ) p=0):
    ∃q,∃hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q,
      ∃hc :IntegralMixedRoadmapAtomic.candidate q=pair u label,
        IntegralMixedRoadmapAtomic.depth q=0 ∧IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 q ∧
        point hn ht ha hR0 u label q hv hc=p:=by
  let r:=IntegralMixedRoadmapFirstSeed.root hn ht ha hR0 u label
  let Q:=IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r
  have HO:IntegralMixedAuxiliaryMarkedIntegerSource.original r=u:=by
    simp only [r,IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedRoadmapFirstSeed.candidate_root,pairFst_pair]
  have HD:n u+3=IntegralMixedAuxiliaryMarkedIntegerSource.number n r+3:=by
    rw [IntegralMixedRoadmapFirstSeed.number_root]
  have HS:HEq (source n t R0 u) Q:=by
    dsimp only [Q]
    rw [IntegralMixedOriginalRegularSource.spatial_source]
    exact (IntegralMixedOriginalRegularSource.source_congr n t R0 _ _ HO).symm
  obtain ⟨pN,HE,HZ,HG⟩:=critical_transport _ _ HD HS p hp hcrit
  obtain ⟨w,hw,hv,HR,HReplay⟩:=IntegralMixedRoadmapFirstSeed.exists_at_replay hn ht ha hR0 u label hg hR pN HZ HG
  let q:=IntegralMixedRoadmapAtomic.packet (pair u label) (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w
  have HPacket:=IntegralMixedRoadmapFirstSeed.packet_eq hn ht ha hR0 u label w
  have hv0 :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
      (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
        (IntegralMixedRoadmapFirstSeed.base u label)) (IntegralMixedRoadmapFirstSeed.base u label) w):=
    Eq.mpr (congrArg (IntegralMixedRoadmapAtomic.Valid hn ht ha hR0) HPacket) hv
  have HP0:=IntegralMixedRoadmapGraph.first_seed_point_of_readback hn ht ha hR0
    (IntegralMixedRoadmapFirstSeed.base u label) w hw hv0 pN HR
  have HPC:=atomic_point_congr hn ht ha hR0 _ _ hv0 hv HPacket
  have HAtomic:HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv) p:=HPC.symm.trans (HP0.trans HE)
  have HC:IntegralMixedRoadmapAtomic.candidate q=pair u label:=IntegralMixedRoadmapGraph.firstSeed_candidate u label w
  have HDepth:IntegralMixedRoadmapAtomic.depth q=0:=by
    change IntegralMixedRoadmapAtomic.depth (IntegralMixedRoadmapAtomic.packet (pair u label)
      (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w)=0
    rw [←HPacket]
    exact IntegralMixedRoadmapSeedResampling.depth_packet _ _ _
  have HI:HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv)
      (IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv):=by
    unfold IntegralMixedRoadmapIdentity.point
    exact cast_point_heq (congrArg (·+1) (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q)) _
  exact ⟨q,hv,HC,HDepth,HReplay,eq_of_heq ((point_heq hn ht ha hR0 u label q hv HC).symm.trans
    (HI.symm.trans HAtomic))⟩

end LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorGeometry

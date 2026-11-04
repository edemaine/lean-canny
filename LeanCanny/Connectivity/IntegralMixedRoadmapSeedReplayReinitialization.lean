/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapFirstSeedReplay
public import LeanCanny.Connectivity.IntegralMixedRoadmapFirstSeedIncidence
public import LeanCanny.Connectivity.IntegralMixedRoadmapPointGlue
/-! # Reinitialize an accepted seed with Replay at the same entire physical point -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open Set LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapAtomic.source IntegralMixedRoadmapAtomic.levels
  IntegralMixedRoadmapSeedResampling.preparedRoot IntegralMixedRoadmapSeedResampling.seedNativePoint
  pointAt

private theorem critical_point_transport {a b :ℕ} (Q :SpatialSource a) (R :SpatialSource b)
    (hd :a=b) (hs :HEq Q R) (p :Fin (a+1)→ℝ)
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

private theorem atomic_point_congr (q r :List Bool) (hq :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hr :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 r) (he :q=r):
    HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hq) (IntegralMixedRoadmapAtomic.point hn ht ha hR0 r hr):=by
  subst r
  rfl

private theorem cast_point_heq {a b :ℕ} (H :a=b) (p :Fin a→ℝ):
    HEq p (fun i:Fin b=>p (Fin.cast H.symm i)):=by cases H;rfl

/-- The old seed need not satisfy Replay. A fresh own word is built with the
prescribed candidate prelude and the SAME entire critical point, then linked
by the actual native whole-point identity edge. -/
theorem seed_reinitialize_replay (u label old :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hc :IntegralMixedRoadmapAtomic.candidate old=pair u label)
    (hd :IntegralMixedRoadmapAtomic.depth old=0)
    (hg :AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (hR :IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u):
    ∃fresh,∃hFresh :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 fresh,
      ∃_hcFresh :IntegralMixedRoadmapAtomic.candidate fresh=IntegralMixedRoadmapAtomic.candidate old,
        IntegralMixedRoadmapAtomic.depth fresh=0 ∧
        IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 fresh ∧
        HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 fresh hFresh)
          (IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv) ∧
        RawReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old fresh:=by
  let r:=IntegralMixedRoadmapFirstSeed.root hn ht ha hR0 u label
  let Q:=IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r
  have HO:IntegralMixedRoadmapAtomic.original old=u:=(congrArg pairFst hc).trans (pairFst_pair u label)
  have HOr:IntegralMixedAuxiliaryMarkedIntegerSource.original r=u:=by
    simp only [r,IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedRoadmapFirstSeed.candidate_root,pairFst_pair]
  have HSold:=IntegralMixedRoadmapAtomic.source_original hn ht ha hR0 old hv
  rw [HO] at HSold
  have HSnew:HEq (source n t R0 u) Q:=by
    dsimp only [Q]
    rw [IntegralMixedOriginalRegularSource.spatial_source]
    exact (IntegralMixedOriginalRegularSource.source_congr n t R0 _ _ HOr).symm
  have HD:(B).parameters.ambient (pairFst ((B).key (IntegralMixedRoadmapAtomic.context old)))=
      IntegralMixedAuxiliaryMarkedIntegerSource.number n r+3:=by
    rw [IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 old,
      IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0 old,HO]
    dsimp only [r]
    rw [IntegralMixedRoadmapFirstSeed.number_root hn ht ha hR0 u label]
  have HOcc:=IntegralMixedRoadmapAtomic.occurrence hn ht ha hR0 old hv
  have HCrit:∀i :Fin ((B).parameters.ambient (pairFst ((B).key (IntegralMixedRoadmapAtomic.context old)))+1),
      i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (IntegralMixedRoadmapAtomic.source hn ht ha hR0 old).low
        (IntegralMixedRoadmapAtomic.source hn ht ha hR0 old).leading
        (IntegralMixedRoadmapAtomic.source hn ht ha hR0 old).degree)).eval₂ (Int.castRingHom ℝ)
      (IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv)=0:=by
    intro i hi
    exact HOcc.critical i (by omega) (by omega)
  obtain ⟨p,HP,HZ,HG⟩:=critical_point_transport _ Q HD (HSold.trans HSnew)
    (IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv) HOcc.zero HCrit
  obtain ⟨w,hw,hFresh,HR,HReplay⟩:=IntegralMixedRoadmapFirstSeed.exists_at_replay hn ht ha hR0 u label hg hR p HZ HG
  let fresh:=IntegralMixedRoadmapAtomic.packet (pair u label) (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w
  have HPacket:=IntegralMixedRoadmapFirstSeed.packet_eq hn ht ha hR0 u label w
  have hv0 :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
      (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
        (IntegralMixedRoadmapFirstSeed.base u label)) (IntegralMixedRoadmapFirstSeed.base u label) w):=
    Eq.mpr (congrArg (IntegralMixedRoadmapAtomic.Valid hn ht ha hR0) HPacket) hFresh
  have HP0:=first_seed_point_of_readback hn ht ha hR0 (IntegralMixedRoadmapFirstSeed.base u label) w hw hv0 p HR
  have HPC:=atomic_point_congr hn ht ha hR0 _ _ hv0 hFresh HPacket
  have HWhole:HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 fresh hFresh)
      (IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv):=HPC.symm.trans (HP0.trans HP)
  have HCandidate:IntegralMixedRoadmapAtomic.candidate fresh=IntegralMixedRoadmapAtomic.candidate old:=
    (firstSeed_candidate (n:=n) u label w).trans hc.symm
  have HDepth:IntegralMixedRoadmapAtomic.depth fresh=0:=by
    change IntegralMixedRoadmapAtomic.depth (IntegralMixedRoadmapAtomic.packet (pair u label)
      (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w)=0
    rw [←HPacket]
    exact IntegralMixedRoadmapSeedResampling.depth_packet _ _ _
  have HOld:HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv)
      (pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old hv rfl):=by
    unfold pointAt
    exact cast_point_heq (congrArg (·+1) (ambient_eq hn ht ha hR0 _ old rfl)) _
  have HNew:HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 fresh hFresh)
      (pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) fresh hFresh HCandidate):=by
    unfold pointAt
    exact cast_point_heq (congrArg (·+1) (ambient_eq hn ht ha hR0 _ fresh HCandidate)) _
  have HEqual:pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old hv rfl=
      pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) fresh hFresh HCandidate:=
    eq_of_heq (HOld.symm.trans (HWhole.symm.trans HNew))
  exact ⟨fresh,hFresh,HCandidate,HDepth,HReplay,HWhole,
    raw_reachable_of_pointAt_eq hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old fresh hv hFresh rfl HCandidate HEqual⟩

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph

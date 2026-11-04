/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapGraphGeometry
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedAcceptance
/-! # A global critical point exists in the actual resampled seed source -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private def HasCritical {a : ℕ} (P : SpatialSource a) : Prop:=
  ∃p : Fin (a+1)→ℝ,
    (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
    ∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) p=0

private theorem critical_transport {a b : ℕ} (P : SpatialSource a) (Q : SpatialSource b)
    (hd : a=b) (he : HEq P Q) : HasCritical P→HasCritical Q :=by
  cases hd
  have h : P=Q:=eq_of_heq he
  cases h
  exact id

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "root" old=>IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old
local notation "Q" old=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (root old)
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
 IntegralMixedRoadmapSeedResampling.preparedRoot IntegralMixedAuxiliaryMarkedIntegerPlan.spatial

theorem exists_prepared_critical (old : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    ∃p : Fin (IntegralMixedAuxiliaryMarkedIntegerSource.number n (root old)+3+1)→ℝ,
      (FermatCriticalHomogenization.polynomial (Q old).low (Q old).leading (Q old).degree).eval₂
        (Int.castRingHom ℝ) p=0 ∧
      ∀i,i.val≠0→(MvPolynomial.pderiv i
        (FermatCriticalHomogenization.polynomial (Q old).low (Q old).leading (Q old).degree)).eval₂
          (Int.castRingHom ℝ) p=0 :=by
  have HO : IntegralMixedAuxiliaryMarkedIntegerSource.original (root old)=IntegralMixedRoadmapAtomic.original old:=by
    simp only [IntegralMixedRoadmapSeedResampling.preparedRoot,IntegralMixedRoadmapAtomic.root,
      IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
      pairFst_pair,IntegralMixedRoadmapAtomic.original,IntegralMixedRoadmapSeedResampling.candidate_packet]
  have HD : n (pairFst (IntegralMixedRoadmapAtomic.candidate old))+3=
      IntegralMixedAuxiliaryMarkedIntegerSource.number n (root old)+3:=by
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,HO,IntegralMixedRoadmapAtomic.original]
  have HS : HEq (originalSource (n:=n) (t:=t) (R0:=R0) (IntegralMixedRoadmapAtomic.candidate old)) (Q old):=by
    rw [IntegralMixedOriginalRegularSource.spatial_source]
    exact (IntegralMixedOriginalRegularSource.source_congr n t R0 _ _ HO).symm
  obtain ⟨p,hp,hg⟩:=exists_global_seed hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old hv rfl
  apply critical_transport _ (Q old) HD HS
  refine ⟨p,hp,?_⟩
  intro i hi
  exact hg i (fun he=>hi (congrArg Fin.val he))

/-- Every accepted vertex admits a fully accepted canonical depth-zero seed.
The critical point and the fresh full word are both constructed internally. -/
theorem exists_resampled_seed (old : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    ∃w,IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
      (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w) ∧
      IntegralMixedRoadmapAtomic.depth
        (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w)=0 ∧
      IntegralMixedRoadmapAtomic.candidate
        (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w)=
          IntegralMixedRoadmapAtomic.candidate old :=by
  obtain ⟨p,hp,hg⟩:=exists_prepared_critical hn ht ha hR0 old hv
  obtain ⟨w,_,hw,_⟩:=IntegralMixedRoadmapSeedResampling.exists_valid hn ht ha hR0 old hv p hp hg
  exact ⟨w,hw,IntegralMixedRoadmapSeedResampling.depth_packet _ _ _,
    IntegralMixedRoadmapSeedResampling.candidate_packet _ _ _⟩

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph

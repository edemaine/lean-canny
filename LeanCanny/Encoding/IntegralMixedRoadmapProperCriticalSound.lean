/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCriticalMetadata
/-! # Accepted no-critical witnesses exclude actual coarse critical heights

The exhaustive critical language is interpreted at its own parent word and
literal checked coarse descriptor. No ghost annihilator root, selected hom,
critical solvability premise or sampler-word transport is used.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters B)
  (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
local notation "K"=>IntegralMixedPhysicalCriticalPrefixes.key n false false
local notation "Q"=>query hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

theorem query_parentWord (q w : List Bool) :
    IntegralMixedPhysicalCriticalQuery.parentWord (Q (pair q w))=w :=by
  simp only [query,IntegralMixedPhysicalCriticalQuery.packet,IntegralMixedPhysicalCriticalQuery.parentWord,
    pairFst_pair,pairSnd_pair]

noncomputable def CoarseCriticalFree (q w : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd : 0<IntegralMixedRoadmapAtomic.depth q)
    (hp : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (radius_binary hR0) false false)
      (Q (pair q w)) (IntegralMixedPhysicalCriticalQuery.parentWord (Q (pair q w)))) : Prop:=
  let HG:=parent_point_good hn ht ha hR0 q w hv hd
  Disjoint (Set.Ioo
    (IntegralMixedPhysicalCriticalInterval.endpointValue hn ht ha (radius_binary hR0) false (Q (pair q w)) hp
      (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.leftWord (Q (pair q w)))))
    (IntegralMixedPhysicalCriticalInterval.endpointValue hn ht ha (radius_binary hR0) false (Q (pair q w)) hp
      (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.rightWord (Q (pair q w))))))
    (IntegralMixedFrozenFrame.realCriticalValues ((G).spatial (K (Q (pair q w))))
      (IntegralMixedFrozenFrame.line
        (IntegralMixedChronologicalFrameCode.descriptor _ _ (IntegralMixedRoadmapProper.labels q) HG.1).frame
        ⟨IntegralMixedRoadmapProper.levelIndex q,HG.2.2.1⟩)
      (IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha (radius_binary hR0) false (Q (pair q w)) hp)
      ⟨IntegralMixedRoadmapProper.levelIndex q,HG.2.2.1⟩)

theorem witness_coarse_critical_free (q wF wP : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd : 0<IntegralMixedRoadmapAtomic.depth q)
    (H : Witness hn ht ha hR0 (pair (pair q wF) wP)) :
    ∃hp : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (radius_binary hR0) false false)
      (Q (pair q wP)) (IntegralMixedPhysicalCriticalQuery.parentWord (Q (pair q wP))),
      CoarseCriticalFree hn ht ha hR0 q wP hv hd hp :=by
  have HP : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (radius_binary hR0) false false)
      (Q (pair q wP)) wP:=by
    simpa only [critical,atomic,parentWord,pairFst_pair,pairSnd_pair] using H.2.1
  have hp : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (radius_binary hR0) false false)
      (Q (pair q wP)) (IntegralMixedPhysicalCriticalQuery.parentWord (Q (pair q wP))):=by
    rw [query_parentWord]
    exact HP
  have HG : IntegralMixedPhysicalCriticalInterval.Guard n false (Q (pair q wP)):=by
    simpa only [critical,atomic,parentWord,pairFst_pair,pairSnd_pair] using H.1
  have HN : Q (pair q wP)∉IntegralMixedPhysicalCriticalInterval.language hn ht ha (radius_binary hR0) false:=by
    simpa only [critical,atomic,parentWord,pairFst_pair,pairSnd_pair] using H.2.2.2.2.2
  refine ⟨hp,?_⟩
  exact (IntegralMixedPhysicalChronologicalCritical.empty_iff hn ht ha (radius_binary hR0) false
    (Q (pair q wP)) (prefixRoot q) wP (IntegralMixedRoadmapProper.labels q)
    (IntegralMixedRoadmapProper.producer false q) (IntegralMixedRoadmapProper.producer true q)
    (IntegralMixedRoadmapProper.levelIndex q) (parent_point_good hn ht ha hR0 q wP hv hd)
    (query_packet_key hn ht ha hR0 q wP) hp HG (query_positive hn ht ha hR0 q wP)
    (t (IntegralMixedRoadmapAtomic.original q)).toData.size (query_degree hn ht ha hR0 q wP)).mp HN

theorem noCritical_coarse_critical_free (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd : 0<IntegralMixedRoadmapAtomic.depth q)
    (H : NoCritical hn ht ha hR0 q) :
    ∃wP,∃hp : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (radius_binary hR0) false false)
      (Q (pair q wP)) (IntegralMixedPhysicalCriticalQuery.parentWord (Q (pair q wP))),
      CoarseCriticalFree hn ht ha hR0 q wP hv hd hp :=by
  obtain ⟨wF,_,wP,_,HW⟩:=H
  obtain ⟨hp,HF⟩:=witness_coarse_critical_free hn ht ha hR0 q wF wP hv hd HW
  exact ⟨wP,hp,HF⟩

end LeanCanny.Encoding.IntegralMixedRoadmapProperCritical

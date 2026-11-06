/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCriticalMetadata
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderChronologicalCritical
/-! # Accepted no-critical witnesses exclude actual coarse critical heights

The exhaustive critical language is interpreted at its own parent word and
literal checked coarse descriptor. No ghost annihilator root, selected hom,
critical solvability premise or sampler-word transport is used.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters B)
  (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
local notation "K"=>FormulaSignSlotRadialProviderCriticalPrefixes.key false
local notation "Q"=>query
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank

theorem query_parentWord (q w : List Bool) :
    IntegralMixedPhysicalCriticalQuery.parentWord (Q (pair q w))=w :=by
  simp only [query,IntegralMixedPhysicalCriticalQuery.packet,IntegralMixedPhysicalCriticalQuery.parentWord,
    pairFst_pair,pairSnd_pair]

noncomputable def CoarseCriticalFree (q w : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (hp : SquareSampleCompleteVertices.Valid
      (FormulaSignSlotRadialProviderCriticalPrefixes.input false)
      (Q (pair q w)) (IntegralMixedPhysicalCriticalQuery.parentWord (Q (pair q w)))) : Prop:=
  let HG:=parent_point_good q w hv hd
  Disjoint (Set.Ioo
    (FormulaSignSlotRadialProviderCriticalInterval.endpointValue (Q (pair q w)) hp
      (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.leftWord (Q (pair q w)))))
    (FormulaSignSlotRadialProviderCriticalInterval.endpointValue (Q (pair q w)) hp
      (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.rightWord (Q (pair q w))))))
    (IntegralMixedFrozenFrame.realCriticalValues ((G).spatial (K (Q (pair q w))))
      (IntegralMixedFrozenFrame.line
        (IntegralMixedChronologicalFrameCode.descriptor _ _ (IntegralMixedRoadmapProper.labels q) HG.1).frame
        ⟨IntegralMixedRoadmapProper.levelIndex q,HG.2.2.1⟩)
      (FormulaSignSlotRadialProviderCriticalInterval.parentValues (Q (pair q w)) hp)
      ⟨IntegralMixedRoadmapProper.levelIndex q,HG.2.2.1⟩)

theorem witness_coarse_critical_free (q wF wP : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (H : Witness (pair (pair q wF) wP)) :
    ∃hp : SquareSampleCompleteVertices.Valid
      (FormulaSignSlotRadialProviderCriticalPrefixes.input false)
      (Q (pair q wP)) (IntegralMixedPhysicalCriticalQuery.parentWord (Q (pair q wP))),
      CoarseCriticalFree q wP hv hd hp :=by
  have HP : SquareSampleCompleteVertices.Valid
      (FormulaSignSlotRadialProviderCriticalPrefixes.input false)
      (Q (pair q wP)) wP:=by
    simpa only [critical,atomic,parentWord,pairFst_pair,pairSnd_pair] using H.2.1
  have hp : SquareSampleCompleteVertices.Valid
      (FormulaSignSlotRadialProviderCriticalPrefixes.input false)
      (Q (pair q wP)) (IntegralMixedPhysicalCriticalQuery.parentWord (Q (pair q wP))):=by
    rw [query_parentWord]
    exact HP
  have HG : FormulaSignSlotRadialProviderCriticalInterval.Guard (Q (pair q wP)):=by
    simpa only [critical,atomic,parentWord,pairFst_pair,pairSnd_pair] using H.1
  have HN : Q (pair q wP)∉FormulaSignSlotRadialProviderCriticalInterval.language:=by
    simpa only [critical,atomic,parentWord,pairFst_pair,pairSnd_pair] using H.2.2.2.2.2
  refine ⟨hp,?_⟩
  exact (FormulaSignSlotRadialProviderChronologicalCritical.empty_iff
    (Q (pair q wP)) (prefixRoot q) wP (IntegralMixedRoadmapProper.labels q)
    (IntegralMixedRoadmapProper.producer false q) (IntegralMixedRoadmapProper.producer true q)
    (IntegralMixedRoadmapProper.levelIndex q) (parent_point_good q wP hv hd)
    (query_packet_key q wP) hp HG (query_positive q wP)
    (LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.equation (FormulaSignSlotRadialProviderAtomic.original q)).toData.size (query_degree q wP)).mp HN

theorem noCritical_coarse_critical_free (q : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (H : NoCritical q) :
    ∃wP,∃hp : SquareSampleCompleteVertices.Valid
      (FormulaSignSlotRadialProviderCriticalPrefixes.input false)
      (Q (pair q wP)) (IntegralMixedPhysicalCriticalQuery.parentWord (Q (pair q wP))),
      CoarseCriticalFree q wP hv hd hp :=by
  obtain ⟨wF,_,wP,_,HW⟩:=H
  obtain ⟨hp,HF⟩:=witness_coarse_critical_free q wF wP hv hd HW
  exact ⟨wP,hp,HF⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical

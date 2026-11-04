/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedNativeReadback
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedFieldRetention
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedFieldReadback
/-! # The native conjunction for a freshly constructed depth-zero seed word -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
local notation "ROOT" old=>preparedRoot hn ht ha hR0 old
local notation "CTX" old=>IntegralMixedRoadmapSeedMetadata.context hn ht ha hR0 old
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  preparedRoot seedOlder seedSelections seedTail
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedRoadmapAtomic.Grammar

private theorem full_query_packet (old w :List Bool) :
    IntegralMixedRoadmapAtomic.fullQuery (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w)=pair (ROOT old) w:=by
  simp only [IntegralMixedRoadmapAtomic.fullQuery,IntegralMixedRoadmapAtomic.root,preparedRoot,
    candidate_packet,payload_packet,word_packet]

theorem valid_of_readback (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (w :List Bool) (hw :SquareSampleCompleteVertices.Valid S (CTX old) w)
    (p :Fin ((B).parameters.ambient (pairFst ((B).key (CTX old)))+1)→ℝ)
    (hr :IntegralMixedRoadmapSeedMetadata.Readback hn ht ha hR0 old w hw p)
    (hm :pair (ROOT old) w∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false) :
    IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w):=by
  have hwA :SquareSampleCompleteVertices.Valid S (IntegralMixedRoadmapAtomic.context (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w)) w:=
    Eq.mpr (congrArg (fun c=>SquareSampleCompleteVertices.Valid S c w)
      (IntegralMixedRoadmapSeedMetadata.packet_context hn ht ha hR0 old w)) hw
  have HG:=grammar hn ht ha hR0 old hv w hwA
  have HC :IntegralMixedAuxiliaryCandidate.Valid hn ht ha
      (IntegralMixedRoadmapAtomic.candidate (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w)):=by
    rw [candidate_packet]
    exact hv.2.1
  have HB :pair (ROOT old) w∈IntegralMixedPhysicalTraceBeforeProbe.language hn ht ha (radius_binary hR0) false:=by
    refine ⟨?_,IntegralMixedRoadmapSeedMetadata.before_probe_holds hn ht ha hR0 old w⟩
    simpa only [IntegralMixedPhysicalMarkedTest.sampleContext,IntegralMixedRoadmapSeedMetadata.context,
      pairFst_pair,pairSnd_pair] using hw
  have HA:=IntegralMixedRoadmapSeedMetadata.all_critical_of_readback hn ht ha hR0 old w hw p hr
  have HP:=IntegralMixedRoadmapSeedMetadata.atomic_companion_of_readback hn ht ha hR0 old w hw p hr
  unfold IntegralMixedRoadmapAtomic.Valid
  refine ⟨HG,HC,?_,?_,?_,HP,?_⟩
  · simpa only [word_packet] using hwA
  · exact Eq.mpr (congrArg (fun q=>q∈IntegralMixedPhysicalTraceBeforeProbe.language hn ht ha (radius_binary hR0) false)
      (full_query_packet hn ht ha hR0 old w)) HB
  · exact Eq.mpr (congrArg (fun q=>q∈IntegralMixedPhysicalGuardScan.language hn ht ha (radius_binary hR0) false)
      (full_query_packet hn ht ha hR0 old w)) HA
  · exact Eq.mpr (congrArg (fun q=>q∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false)
      (full_query_packet hn ht ha hR0 old w)) hm

private theorem prepared_candidate_eq (old :List Bool) :
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate (IntegralMixedRoadmapAtomic.root old)=
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate (ROOT old):=by
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapAtomic.root,
    preparedRoot,candidate_packet,payload_packet,pairFst_pair]

private theorem marked_of_prelude_fields (old :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX old) w)
    (he :∀i<number n (IntegralMixedRoadmapAtomic.root old)+8,
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context old) (IntegralMixedRoadmapAtomic.word old)
        (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv) i=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX old) w hw i) :
    pair (ROOT old) w∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false:=by
  apply IntegralMixedPhysicalMarkedRetention.language_transfer_fields hn ht ha hR0
    (IntegralMixedRoadmapAtomic.root old) (ROOT old) (IntegralMixedRoadmapAtomic.word old) w
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv) hw
    (prepared_candidate_eq hn ht ha hR0 old) he
  exact hv.2.2.2.2.2.2

/-- One genuine global critical point yields a fresh, fully accepted seed word.
The word is sampled at its own prepared root; every critical block reads the
chosen point, and the initial marked data comes from the old accepted word. -/
theorem exists_valid (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (p :Fin ((P).ambient (ROOT old)+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial (Q (ROOT old)).low
      (Q (ROOT old)).leading (Q (ROOT old)).degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg :∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q (ROOT old)).low
        (Q (ROOT old)).leading (Q (ROOT old)).degree)).eval₂ (Int.castRingHom ℝ) p=0) :
    ∃w,∃hw :SquareSampleCompleteVertices.Valid S (CTX old) w,
      IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
        (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w) ∧
      IntegralMixedRoadmapSeedMetadata.Readback hn ht ha hR0 old w hw (seedNativePoint hn ht ha hR0 old p):=by
  obtain ⟨u,w,hw,_,HJ,_,_,HB,HV⟩:=exists_seed_word hn ht ha hR0 old hv p hp hg
  have HJF :FieldJoint hn ht ha hR0 old w hw u:=HJ
  have HVF :FieldValues hn ht ha hR0 old hv p u:=HV
  have HR :IntegralMixedRoadmapSeedMetadata.Readback hn ht ha hR0 old w hw
      (seedNativePoint hn ht ha hR0 old p):=by
    constructor
    · intro a ha0
      exact geometricPoint_of_columns hn ht ha hR0 old w hw p u
        (seed_candidates hn ht ha hR0 _ w hw u HJ) HB a ha0
    · intro a ha0
      have HE:=seed_selected_field hn ht ha hR0 old hv p u w hw HJF HVF a ha0
      refine HE.trans ?_
      unfold seedNativePoint
      apply congrArg p
      apply Fin.ext
      have HS:=IntegralMixedRoadmapSeedMetadata.critical_selected hn ht ha hR0 old a ha0
      rw [←prepared_dimension hn ht ha hR0 old] at HS
      exact HS.symm
  have HM :pair (ROOT old) w∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false:=by
    apply marked_of_prelude_fields hn ht ha hR0 old hv w hw
    intro i hi
    have HN:=IntegralMixedMarkedPreludeCongruence.number_eq (n:=n)
      (IntegralMixedRoadmapAtomic.root old) (ROOT old) (prepared_candidate_eq hn ht ha hR0 old)
    exact (seed_prelude_field hn ht ha hR0 old hv p u w hw HJF HVF i (by omega)).symm
  exact ⟨w,hw,valid_of_readback hn ht ha hR0 old hv w hw _ HR HM,HR⟩

end LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedAcceptance
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCandidateAtRadius
/-! # Candidate-direct syntax for the first canonical seed

The metadata packet is never assumed accepted. Candidate validity alone
supplies its original byte bounds; the full word is constructed later.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapFirstSeed
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def base (u label :List Bool):=IntegralMixedRoadmapAtomic.packet (pair u label) [] []

theorem candidate_base (u label :List Bool) :IntegralMixedRoadmapAtomic.candidate (base u label)=pair u label:=by
  simp only [base,IntegralMixedRoadmapAtomic.packet,IntegralMixedRoadmapAtomic.candidate,pairFst_pair]
theorem original_base (u label :List Bool) :IntegralMixedRoadmapAtomic.original (base u label)=u:=by
  simp only [IntegralMixedRoadmapAtomic.original,candidate_base,pairFst_pair]

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)

noncomputable def root (u label :List Bool):=
  IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 (base u label)

theorem dimension_base (u label :List Bool) :
    IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label)=n u+3:=by
  rw [IntegralMixedRoadmapAtomic.dimension_eq,original_base]

theorem candidate_root (u label :List Bool) :IntegralMixedAuxiliaryMarkedIntegerSource.candidate
    (root hn ht ha hR0 u label)=pair u label:=by
  simp only [root,IntegralMixedRoadmapSeedResampling.preparedRoot,IntegralMixedRoadmapAtomic.root,
    IntegralMixedRoadmapSeedResampling.candidate_packet,candidate_base,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,pairFst_pair]

theorem number_root (u label :List Bool) :IntegralMixedAuxiliaryMarkedIntegerSource.number n
    (root hn ht ha hR0 u label)=n u:=by
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    candidate_root,pairFst_pair]

theorem packet_eq (u label w :List Bool) :
    IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label))
      (base u label) w=IntegralMixedRoadmapAtomic.packet (pair u label)
        (IntegralMixedRoadmapSeedResampling.payload (n u+3)) w:=by
  simp only [IntegralMixedRoadmapSeedResampling.packet,dimension_base,candidate_base]

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.width IntegralMixedRoadmapAtomic.sourceCap
  IntegralMixedRoadmapAtomic.scalarBudget root base

theorem checked (u label w :List Bool)
    (hc :IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair u label)) :
    IntegralMixedRoadmapChain.Checked (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label))
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0
        (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label)) (base u label) w))
      (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0
        (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label)) (base u label) w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (base u label))
      (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha (base u label))
      (IntegralMixedRoadmapSeedResampling.payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label))):=by
  apply IntegralMixedRoadmapChain.complete_seed_checked
  · have HL :label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha u:=by
      simpa only [pairFst_pair,pairSnd_pair] using hc.1.1.le
    let metadata:=pair (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapSeedResampling.payload
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label)))) []
    have HW:=IntegralMixedRoadmapWidth.width_le_scalarBudget hn ht ha u label metadata HL
    unfold IntegralMixedRoadmapAtomic.width IntegralMixedPhysicalMarkedPlan.bank
    simp only [Bool.false_eq_true,ite_false,IntegralMixedAuxiliaryMarkedRecordPlan.bank]
    rw [IntegralMixedRoadmapWidth.certified_width]
    simpa only [IntegralMixedRoadmapAtomic.root,IntegralMixedRoadmapSeedResampling.candidate_packet,
      IntegralMixedRoadmapSeedResampling.payload_packet,candidate_base,pairSnd_pair,
      IntegralMixedRoadmapAtomic.scalarBudget,original_base,metadata] using HW
  · exact IntegralMixedRoadmapAtomic.sourceCap_le hn ht ha hR0 _

theorem grammar (u label w :List Bool)
    (hc :IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair u label))
    (hw :SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (IntegralMixedRoadmapAtomic.context (IntegralMixedRoadmapSeedResampling.packet
        (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label)) (base u label) w)) w) :
    IntegralMixedRoadmapAtomic.Grammar hn ht ha hR0 (IntegralMixedRoadmapSeedResampling.packet
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label)) (base u label) w):=by
  have HC:=checked hn ht ha hR0 u label w hc
  have HL :label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha u:=by
    simpa only [pairFst_pair,pairSnd_pair] using hc.1.1.le
  have HP :IntegralMixedRoadmapAtomic.Canonical (IntegralMixedRoadmapSeedResampling.packet
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label)) (base u label) w):=by
    constructor
    · simp only [IntegralMixedRoadmapSeedResampling.packet,IntegralMixedRoadmapAtomic.packet,
        IntegralMixedRoadmapAtomic.payload,IntegralMixedRoadmapAtomic.word,IntegralMixedRoadmapAtomic.candidate,
        pairFst_pair,pairSnd_pair]
    · simp only [IntegralMixedRoadmapSeedResampling.candidate_packet,IntegralMixedRoadmapSeedResampling.original_packet,
        candidate_base,original_base,pairSnd_pair]
  have HC' :IntegralMixedRoadmapChain.Checked (n u+3)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 (IntegralMixedRoadmapSeedResampling.packet
        (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label)) (base u label) w))
      (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 (IntegralMixedRoadmapSeedResampling.packet
        (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label)) (base u label) w))
      (n u+8) (IntegralMixedRoadmapWidth.scalarBudget hn ht ha u)
      (IntegralMixedRoadmapSeedResampling.payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label))):=by
    simpa only [IntegralMixedRoadmapAtomic.dimension_eq,IntegralMixedRoadmapAtomic.initial_eq,
      IntegralMixedRoadmapAtomic.scalarBudget,original_base] using HC
  have HE :(IntegralMixedRoadmapChain.records HC').root
      (IntegralMixedRoadmapChain.seed _ _ _ ⟨0,by omega⟩) (IntegralMixedRoadmapChain.reservedProbe HC') (pair u label) []=
      IntegralMixedRoadmapAtomic.root (IntegralMixedRoadmapSeedResampling.packet
        (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (base u label)) (base u label) w):=by
    simp only [IntegralMixedRoadmapRecordChain.Records.root,←IntegralMixedRoadmapChain.raw_paddedWord HC',
      IntegralMixedRoadmapAtomic.root,IntegralMixedRoadmapSeedResampling.payload_packet,
      IntegralMixedRoadmapSeedResampling.candidate_packet,candidate_base]
  have HW:=IntegralMixedRoadmapWidth.word_length_le_vertexBudget hn ht ha (radius_binary hR0) u label HL
    (IntegralMixedRoadmapChain.records HC') (IntegralMixedRoadmapChain.seed _ _ _ ⟨0,by omega⟩)
    (IntegralMixedRoadmapChain.reservedProbe HC') w (by
      simpa only [IntegralMixedRoadmapWidth.dimension,IntegralMixedRoadmapWidth.initial,HE,
        IntegralMixedRoadmapAtomic.context] using hw)
  refine ⟨HP,?_,?_⟩
  · simpa only [IntegralMixedRoadmapSeedResampling.dimension_packet,IntegralMixedRoadmapSeedResampling.initial_packet,
      IntegralMixedRoadmapAtomic.scalarBudget,IntegralMixedRoadmapSeedResampling.original_packet,
      IntegralMixedRoadmapSeedResampling.payload_packet] using HC
  · simpa only [IntegralMixedRoadmapSeedResampling.word_packet,IntegralMixedRoadmapAtomic.wordBudget,
      IntegralMixedRoadmapSeedResampling.original_packet,original_base] using HW

end LeanCanny.Encoding.IntegralMixedRoadmapFirstSeed

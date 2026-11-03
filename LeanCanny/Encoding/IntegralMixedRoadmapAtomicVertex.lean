/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicControls
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceBeforeProbe
public import LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionSemantics
public import LeanCanny.Encoding.IntegralMixedRoadmapOwnHeightCode
/-! # Original-only polynomial-space validity of one atomic roadmap vertex

One full word validates all meaningful old cuts, all creating critical
correlations, the latest all-coordinate companions and the original leaves.
The reserved record is not required to be a cut. No midpoint mode occurs.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapAtomic
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

noncomputable def Valid (q :List Bool) :Prop:=Grammar hn ht ha hR0 q ∧
  IntegralMixedAuxiliaryCandidate.Valid hn ht ha (candidate q) ∧
  SquareSampleCompleteVertices.Valid S (context q) (word q) ∧
  fullQuery q∈IntegralMixedPhysicalTraceBeforeProbe.language hn ht ha (radius_binary hR0) false ∧
  fullQuery q∈IntegralMixedPhysicalGuardScan.language hn ht ha (radius_binary hR0) false ∧
  companionQuery (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q∈
    IntegralMixedPhysicalPointCompanionScan.language hn ht ha (radius_binary hR0) false ∧
  fullQuery q∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false

noncomputable def language :Language:={q |Valid hn ht ha hR0 q}

theorem evaluator :SpaceFunction (fun q=>[decide (Valid hn ht ha hR0 q)]) :=by
  have EG:=SpaceFunction.ofFP _ (grammar_FP hn ht ha hR0).flag_mem_FP
  have EC:=((IntegralMixedAuxiliaryCandidate.decider hn ht ha).precompose candidate candidate_FP).flagEvaluator
  have EV:=((SquareSampleCompleteVertices.decider (IntegralMixedPhysicalMarkedNative.access hn ht ha (radius_binary hR0) false)).precompose
    sampleQuery sampleQuery_FP).flagEvaluator
  have ET:=((IntegralMixedPhysicalTraceBeforeProbe.decider hn ht ha (radius_binary hR0) false).precompose fullQuery fullQuery_FP).flagEvaluator
  have ER:=IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha (radius_binary hR0) false
  have EA:=((IntegralMixedPhysicalGuardScan.decider hn ht ha (radius_binary hR0) false ER).precompose fullQuery fullQuery_FP).flagEvaluator
  have EP:=((IntegralMixedPhysicalPointCompanionScan.decider hn ht ha (radius_binary hR0) false).precompose
    (fun q=>companionQuery (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q)
    (native_companionQuery hn ht ha hR0)).flagEvaluator
  have EM:=((IntegralMixedPhysicalMarkedNative.decider hn ht ha (radius_binary hR0) false).precompose fullQuery fullQuery_FP).flagEvaluator
  exact (EG.andFlags (EC.andFlags (EV.andFlags (ET.andFlags (EA.andFlags (EP.andFlags EM)))))).congr
    (funext fun q=>by
      apply congrArg List.singleton
      apply Bool.eq_iff_iff.mpr
      simp only [Valid,Set.mem_preimage,IntegralMixedAuxiliaryCandidate.language,
        SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,sampleQuery,pairFst_pair,pairSnd_pair,
        List.cons.injEq,and_true,decide_eq_true_eq])

theorem decider :SpaceDecider (language hn ht ha hR0):=by
  apply (evaluator hn ht ha hR0).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE :language hn ht ha hR0∈PSPACE:=(decider hn ht ha hR0).mem_PSPACE

theorem full_valid (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    SquareSampleCompleteVertices.Valid S (context q) (word q):=hv.2.2.1
theorem checked (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    IntegralMixedRoadmapChain.Checked (dimension hn ht ha hR0 q) (width hn ht ha hR0 q)
      (sourceCap hn ht ha hR0 q) (initial hn ht ha hR0 q) (scalarBudget hn ht ha q) (payload q):=hv.1.2.1
theorem depth_le (q :List Bool) (hv :Valid hn ht ha hR0 q) :depth q≤dimension hn ht ha hR0 q:=
  (checked hn ht ha hR0 q hv).1
theorem raw_count (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    WordListRecords.count (IntegralMixedRoadmapChain.raw (payload q))=
      IntegralMixedRoadmapRecordChain.probedRecordBound (dimension hn ht ha hR0 q):=
  (checked hn ht ha hR0 q hv).2.2.2.2.2.2.1
theorem latest_block_end (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+free (dimension hn ht ha hR0 q) q=
      endBirth (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q :=
  block_end _ _ q (depth_le hn ht ha hR0 q hv)
theorem word_bound (q :List Bool) (hv :Valid hn ht ha hR0 q) :(word q).length≤wordBudget hn ht ha hR0 q:=hv.1.2.2

theorem raw_byte_bound (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    (IntegralMixedRoadmapChain.raw (payload q)).length≤IntegralMixedRoadmapWidth.tableBudget hn ht ha (original q) :=by
  have HR:=IntegralMixedRoadmapChain.raw_length_le (checked hn ht ha hR0 q hv)
  simpa only [dimension_eq hn ht ha hR0 q,initial_eq hn ht ha hR0 q,scalarBudget,
    IntegralMixedRoadmapWidth.tableBudget,IntegralMixedRoadmapWidth.recordBudget,
    IntegralMixedRoadmapWidth.dimension,IntegralMixedRoadmapWidth.initial] using HR

theorem candidate_byte_bound (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    (candidate q).length≤IntegralMixedRoadmapWidth.candidateBudget hn ht ha (original q) :=by
  have HL :(pairSnd (candidate q)).length=IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (original q):=hv.2.1.1.1
  have HC:=congrArg List.length hv.1.1.2
  simp only [pair_length] at HC
  unfold IntegralMixedRoadmapWidth.candidateBudget
  omega

theorem context_byte_bound (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    (context q).length≤IntegralMixedRoadmapWidth.contextBudget hn ht ha (original q) :=by
  have HR:=raw_byte_bound hn ht ha hR0 q hv
  have HC:=candidate_byte_bound hn ht ha hR0 q hv
  simp only [context,root,pair_length,List.length_nil]
  unfold IntegralMixedRoadmapWidth.contextBudget
  omega

theorem own_height_record (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    WordList.get (IntegralMixedRoadmapChain.raw (payload q))
      (IntegralMixedRoadmapChain.rawStart (dimension hn ht ha hR0 q) (payload q) (depth q)-1)=
    IntegralMixedChronologicalFrameCode.code (dimension hn ht ha hR0 q) (frozen q) (depth q) (depth q) :=
  IntegralMixedRoadmapOwnHeightCode.checked_own_height_record (checked hn ht ha hR0 q hv) (depth q) le_rfl

theorem companion_valid (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    companionQuery (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q∈
      IntegralMixedPhysicalPointCompanionScan.language hn ht ha (radius_binary hR0) false :=hv.2.2.2.2.2.1

attribute [local irreducible] root context payload candidate word dimension initial width sourceCap
  scalarBudget wordBudget

noncomputable def point (q :List Bool) (hv :Valid hn ht ha hR0 q) :=
  IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
    (context q) (word q) (full_valid hn ht ha hR0 q hv)
    (anchor (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q)

attribute [local irreducible] point IntegralMixedPhysicalPointCompanionScan.geometricPoint
  IntegralMixedPhysicalPointCompanionScan.retained IntegralMixedPhysicalPointCompanionScan.selected
  IntegralMixedPhysicalMarkedPlan.native IntegralMixedPhysicalMarkedPlan.tables
  IntegralMixedFramedHistoryFamilyBits.family IntegralFramedPhysicalCriticalGuardTest.value
  IntegralMixedPhysicalPointEquality.value IntegralMixedPhysicalPointEquality.block
  IntegralMixedFramedPhysicalIndex.prefixArity UniformIntegralPowerSchedule.physical

noncomputable def Captured (c w :List Bool) (hv :SquareSampleCompleteVertices.Valid S c w)
    (a f k :ℕ) :Prop:=∀j<k,
  ∃hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false c (f+j),
    IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false c w hv (f+j)=
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false c w hv a ∧
    IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false c w hv (f+j) hb=
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false c w hv a
        ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false c (f+j),
          IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false c (f+j) hb⟩

theorem packet_active (c w :List Bool) (a f k :ℕ)
    (hp :pair (pair c w) (IntegralMixedPhysicalPointCompanionScan.descriptor a f k)∈
      IntegralMixedPhysicalPointCompanionScan.language hn ht ha (radius_binary hR0) false) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false c a :=by
  have HA:=hp.2.1.2.1
  simp only [IntegralMixedPhysicalPointCompanionScan.anchorQuery,IntegralMixedPhysicalPointCompanionScan.anchor,
    IntegralMixedPhysicalPointCompanionScan.descriptor,
    pairFst_pair,pairSnd_pair,List.length_replicate] at HA
  exact HA

theorem anchor_active (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (context q)
      (anchor (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q) :=
  packet_active hn ht ha hR0 (context q) (word q)
    (anchor (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q)
    (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q) (free (dimension hn ht ha hR0 q) q)
    (companion_valid hn ht ha hR0 q hv)

theorem companion_holds (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    IntegralMixedPhysicalPointCompanionScan.holds hn ht ha (radius_binary hR0) false
      (pair (pair (context q) (word q))
        (IntegralMixedPhysicalPointCompanionScan.descriptor
          (anchor (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q)
          (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q) (free (dimension hn ht ha hR0 q) q))) :=
  (companion_valid hn ht ha hR0 q hv).2.2

theorem captured_iff (c w :List Bool) (hv :SquareSampleCompleteVertices.Valid S c w) (a f k :ℕ)
    (hAnchor :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false c a) :
    IntegralMixedPhysicalPointCompanionScan.holds hn ht ha (radius_binary hR0) false
      (pair (pair c w) (IntegralMixedPhysicalPointCompanionScan.descriptor a f k)) ↔
    Captured hn ht ha hR0 c w hv a f k :=
  IntegralMixedPhysicalPointCompanionScan.holds_iff_points hn ht ha (radius_binary hR0) false c w hv a f k hAnchor

theorem companions (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    Captured hn ht ha hR0 (context q) (word q) (full_valid hn ht ha hR0 q hv)
      (anchor (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q)
      (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q) (free (dimension hn ht ha hR0 q) q) :=
  (captured_iff hn ht ha hR0 (context q) (word q) (full_valid hn ht ha hR0 q hv)
    (anchor (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q)
    (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q) (free (dimension hn ht ha hR0 q) q)
    (anchor_active hn ht ha hR0 q hv)).mp (companion_holds hn ht ha hR0 q hv)

theorem own_height_point (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
      (context q) (word q) (full_valid hn ht ha hR0 q hv)
      (endBirth (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-1)=point hn ht ha hR0 q hv :=by
  unfold point
  have HD:=depth_le hn ht ha hR0 q hv
  have HF :0<free (dimension hn ht ha hR0 q) q :=by unfold free;omega
  obtain ⟨hb,HP,_⟩:=companions hn ht ha hR0 q hv (free (dimension hn ht ha hR0 q) q-1) (by omega)
  have HE:=latest_block_end hn ht ha hR0 q hv
  have HA :first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+
      (free (dimension hn ht ha hR0 q) q-1)=endBirth (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-1 :=by omega
  exact (congrArg (IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
    (context q) (word q) (full_valid hn ht ha hR0 q hv)) HA.symm).trans HP
end LeanCanny.Encoding.IntegralMixedRoadmapAtomic

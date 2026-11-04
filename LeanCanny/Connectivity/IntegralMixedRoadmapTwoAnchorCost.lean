/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapAnchorIncidence
/-! # Native bounded comparison of two marked component anchors

The two candidate labels may differ. Each anchor has its own accepted depth-zero
word and native Replay, and the standalone identity query compares its entire
actual point. Geometric attachment is separate from this cost theorem.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorCost
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- The query is `pair original (pair candidateLabelA candidateLabelB)`. -/
def candidate (side :Bool) (q :List Bool):=pair (pairFst q)
  (if side then pairSnd (pairSnd q) else pairFst (pairSnd q))
theorem candidate_FP (side :Bool):candidate side∈FP:=by cases side <;> polytime [candidate]
def input (z :List Bool):=pairFst (pairFst z)
def seed (side :Bool) (z :List Bool):=IntegralMixedRoadmapWordLabel.decode
  (if side then pairSnd z else pairSnd (pairFst z))
theorem input_FP :input∈FP:=by polytime [input]
theorem seed_FP (side :Bool):seed side∈FP:=by
  cases side <;> exact mem_FP_comp (by polytime) IntegralMixedRoadmapWordLabel.decode_FP
def incidenceQuery (side :Bool) (z :List Bool):=pair (candidate side (input z)) (seed side z)
theorem incidenceQuery_FP (side :Bool):incidenceQuery side∈FP:=
  mem_FP_pair (mem_FP_comp input_FP (candidate_FP side)) (seed_FP side)

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)

noncomputable def pointQuery (z :List Bool):=IntegralMixedRoadmapIdentity.query hn ht ha hR0
  (pair (seed false z) (seed true z))
theorem pointQuery_FP :pointQuery hn ht ha hR0∈FP:=
  mem_FP_comp (mem_FP_pair (seed_FP false) (seed_FP true))
    (IntegralMixedRoadmapIdentity.query_FP hn ht ha hR0)

noncomputable def seedLanguage (side :Bool):Language:={z |
  IntegralMixedRoadmapAtomic.depth (seed side z)=0 ∧
  IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 (seed side z) ∧
  incidenceQuery side z∈IntegralMixedRoadmapAnchorIncidence.language hn ht ha hR0}

theorem seed_decider (side :Bool):SpaceDecider (seedLanguage hn ht ha hR0 side):=by
  have ED:=SpaceFunction.ofFP _
    ((BinaryFn.ofUnary (IntegralMixedRoadmapAtomic.depth_unary.comp (seed_FP side))).eq
      (BinaryFn.ofUnary (UnaryFn.const 0))).flag_mem_FP
  have ER:=((IntegralMixedRoadmapMarkedPrelude.decider hn ht ha hR0).precompose
    (seed side) (seed_FP side)).flagEvaluator
  have EI:=((IntegralMixedRoadmapAnchorIncidence.decider hn ht ha hR0).precompose
    (incidenceQuery side) (incidenceQuery_FP side)).flagEvaluator
  apply (ED.andFlags (ER.andFlags EI)).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [seedLanguage,IntegralMixedRoadmapMarkedPrelude.language,Set.mem_ofPred_eq,
    Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq]

noncomputable def witnessLanguage :Language:={z |
  z∈seedLanguage hn ht ha hR0 false ∧z∈seedLanguage hn ht ha hR0 true ∧
  pointQuery hn ht ha hR0 z∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0)}

theorem witness_decider :SpaceDecider (witnessLanguage hn ht ha hR0):=by
  have EA:=(seed_decider hn ht ha hR0 false).flagEvaluator
  have EB:=(seed_decider hn ht ha hR0 true).flagEvaluator
  have EP:=((IntegralMixedPhysicalFieldEqualityList.decider hn ht ha (radius_binary hR0)).precompose
    _ (pointQuery_FP hn ht ha hR0)).flagEvaluator
  apply (EA.andFlags (EB.andFlags EP)).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [witnessLanguage,Set.mem_ofPred_eq,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq]

noncomputable def width (side :Bool) (q :List Bool):=
  IntegralMixedRoadmapGraph.width hn ht ha hR0 (candidate side q)
theorem width_unary (side :Bool):UnaryFn (width hn ht ha hR0 side):=
  (IntegralMixedRoadmapGraph.width_unary hn ht ha hR0).comp (candidate_FP side)

noncomputable def innerLanguage :Language:={r |∃wordB :List Bool,
  wordB.length=width hn ht ha hR0 true (pairFst r) ∧pair r wordB∈witnessLanguage hn ht ha hR0}
theorem inner_decider :SpaceDecider (innerLanguage hn ht ha hR0):=by
  have E:=(witness_decider hn ht ha hR0).flagEvaluator.exists_words
    ((width_unary hn ht ha hR0 true).comp pairFst_mem_FP)
  apply E.decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro r
  simp only [innerLanguage,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

noncomputable def boundedLanguage :Language:={q |∃wordA :List Bool,
  wordA.length=width hn ht ha hR0 false q ∧pair q wordA∈innerLanguage hn ht ha hR0}
theorem bounded_decider :SpaceDecider (boundedLanguage hn ht ha hR0):=by
  have E:=(inner_decider hn ht ha hR0).flagEvaluator.exists_words (width_unary hn ht ha hR0 false)
  apply E.decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [boundedLanguage,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

noncomputable def Seeds (q a b :List Bool):Prop:=
  IntegralMixedRoadmapAtomic.depth a=0 ∧IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 a ∧
  IntegralMixedRoadmapAnchorIncidence.Incidence hn ht ha hR0 (candidate false q) a ∧
  IntegralMixedRoadmapAtomic.depth b=0 ∧IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 b ∧
  IntegralMixedRoadmapAnchorIncidence.Incidence hn ht ha hR0 (candidate true q) b ∧
  IntegralMixedRoadmapIdentity.query hn ht ha hR0 (pair a b)∈
    IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0)
noncomputable def language :Language:={q |∃a b,Seeds hn ht ha hR0 q a b}

theorem witness_packet_iff (q wordA wordB :List Bool):
    pair (pair q wordA) wordB∈witnessLanguage hn ht ha hR0 ↔
      Seeds hn ht ha hR0 q (IntegralMixedRoadmapWordLabel.decode wordA)
        (IntegralMixedRoadmapWordLabel.decode wordB):=by
  simp only [witnessLanguage,seedLanguage,Seeds,IntegralMixedRoadmapAnchorIncidence.language,
    Set.mem_ofPred_eq,incidenceQuery,input,seed,pointQuery,pairFst_pair,pairSnd_pair,
    Bool.false_eq_true,ite_false,ite_true,and_assoc]

theorem bounded_iff (q :List Bool):
    q∈boundedLanguage hn ht ha hR0 ↔q∈language hn ht ha hR0:=by
  constructor
  · rintro ⟨wordA,_,wordB,_,HW⟩
    exact ⟨IntegralMixedRoadmapWordLabel.decode wordA,IntegralMixedRoadmapWordLabel.decode wordB,
      (witness_packet_iff hn ht ha hR0 q wordA wordB).mp HW⟩
  · rintro ⟨a,b,H⟩
    obtain ⟨_,_,HA⟩:=H.2.2.1
    obtain ⟨_,_,HB⟩:=H.2.2.2.2.2.1
    refine ⟨IntegralMixedRoadmapGraph.label hn ht ha hR0 (candidate false q) a,
      IntegralMixedRoadmapGraph.label_length hn ht ha hR0 _ a HA.1 HA.2.2.1,
      IntegralMixedRoadmapGraph.label hn ht ha hR0 (candidate true q) b,?_,?_⟩
    · simpa only [pairFst_pair,width] using
        IntegralMixedRoadmapGraph.label_length hn ht ha hR0 _ b HB.1 HB.2.2.1
    · apply (witness_packet_iff hn ht ha hR0 q _ _).mpr
      simpa only [IntegralMixedRoadmapGraph.label_decode] using H

theorem decider :SpaceDecider (language hn ht ha hR0):=
  (bounded_decider hn ht ha hR0).congr (Set.ext (bounded_iff hn ht ha hR0))
theorem mem_PSPACE :language hn ht ha hR0∈PSPACE:=(decider hn ht ha hR0).mem_PSPACE

private theorem incidence_dimension_eq (q a b :List Bool)
    (HA :IntegralMixedRoadmapAnchorIncidence.Incidence hn ht ha hR0 (candidate false q) a)
    (HB :IntegralMixedRoadmapAnchorIncidence.Incidence hn ht ha hR0 (candidate true q) b):
    IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 a=
      IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 b:=by
  obtain ⟨_,_,HRA⟩:=HA
  obtain ⟨_,_,HRB⟩:=HB
  rw [IntegralMixedRoadmapAtomic.dimension_eq,IntegralMixedRoadmapAtomic.dimension_eq]
  have HAc:=congrArg pairFst HRA.2.2.1
  have HBc:=congrArg pairFst HRB.2.2.1
  simp only [candidate,pairFst_pair] at HAc HBc
  exact congrArg (fun v=>n v+3) (HAc.trans HBc.symm)

/-- The entire points agree even though the candidate labels may differ. -/
theorem language_iff_points (q :List Bool):q∈language hn ht ha hR0 ↔
    ∃a b,∃hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a,
      ∃hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b,
      IntegralMixedRoadmapAtomic.depth a=0 ∧IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 a ∧
      IntegralMixedRoadmapAnchorIncidence.Incidence hn ht ha hR0 (candidate false q) a ∧
      IntegralMixedRoadmapAtomic.depth b=0 ∧IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 b ∧
      IntegralMixedRoadmapAnchorIncidence.Incidence hn ht ha hR0 (candidate true q) b ∧
      HEq (IntegralMixedRoadmapIdentity.point hn ht ha hR0 a hA)
        (IntegralMixedRoadmapIdentity.point hn ht ha hR0 b hB):=by
  constructor
  · rintro ⟨a,b,HDa,HRa,HIa,HDb,HRb,HIb,HE⟩
    have hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a:=by
      obtain ⟨_,_,HRA⟩:=HIa
      exact HRA.1
    have hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b:=by
      obtain ⟨_,_,HRB⟩:=HIb
      exact HRB.1
    exact ⟨a,b,hA,hB,HDa,HRa,HIa,HDb,HRb,HIb,
      (IntegralMixedRoadmapIdentity.query_iff hn ht ha hR0 a b hA hB
        (incidence_dimension_eq hn ht ha hR0 q a b HIa HIb)).mp HE⟩
  · rintro ⟨a,b,hA,hB,HDa,HRa,HIa,HDb,HRb,HIb,HE⟩
    exact ⟨a,b,HDa,HRa,HIa,HDb,HRb,HIb,
      (IntegralMixedRoadmapIdentity.query_iff hn ht ha hR0 a b hA hB
        (incidence_dimension_eq hn ht ha hR0 q a b HIa HIb)).mpr HE⟩

end LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorCost

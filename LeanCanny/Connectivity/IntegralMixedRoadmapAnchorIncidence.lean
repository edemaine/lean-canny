/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapGraphCoding
public import LeanCanny.Encoding.IntegralMixedRoadmapMarkerAt
public import LeanCanny.Computation.SpaceFunctionWordExistence
/-! # Native bounded search for a reachable terminal marker

This is a concrete PSPACE predicate. Its geometric marked-component
interpretation is separate from the search and is proved using attachment.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapAnchorIncidence
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def marker (q :List Bool):=IntegralMixedRoadmapWordLabel.decode (pairSnd q)
def reachQuery (q :List Bool):=pair (pairFst (pairFst q)) (pair (pairSnd (pairFst q)) (marker q))
theorem marker_FP :marker∈FP:=mem_FP_comp pairSnd_mem_FP IntegralMixedRoadmapWordLabel.decode_FP
theorem reachQuery_FP :reachQuery∈FP:=by polytime [reachQuery,marker,IntegralMixedRoadmapWordLabel.decode]

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)

noncomputable def witnessLanguage :Language:={q |
  marker q∈IntegralMixedRoadmapMarkerAt.language hn ht ha hR0 ∧
    reachQuery q∈nativeReachLanguage hn ht ha hR0}

theorem witness_decider :SpaceDecider (witnessLanguage hn ht ha hR0):=by
  have EM:=((IntegralMixedRoadmapMarkerAt.decider hn ht ha hR0).precompose marker marker_FP).flagEvaluator
  have ER:=((native_reach_decider hn ht ha hR0).precompose reachQuery reachQuery_FP).flagEvaluator
  apply (EM.andFlags ER).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [witnessLanguage,Set.mem_ofPred_eq,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq]

noncomputable def width (q :List Bool):=IntegralMixedRoadmapGraph.width hn ht ha hR0 (pairFst q)
theorem width_unary :UnaryFn (width hn ht ha hR0):=
  (IntegralMixedRoadmapGraph.width_unary hn ht ha hR0).comp pairFst_mem_FP

noncomputable def boundedLanguage :Language:={q |∃word :List Bool,
  word.length=width hn ht ha hR0 q ∧pair q word∈witnessLanguage hn ht ha hR0}

theorem bounded_decider :SpaceDecider (boundedLanguage hn ht ha hR0):=by
  have E:=(witness_decider hn ht ha hR0).flagEvaluator.exists_words (width_unary hn ht ha hR0)
  apply E.decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [boundedLanguage,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

/-- A native marker exists in the actual fixed-candidate reachable component. -/
noncomputable def Incidence (candidate seed :List Bool):Prop:=∃terminal,
  terminal∈IntegralMixedRoadmapMarkerAt.language hn ht ha hR0 ∧
    RawReachable hn ht ha hR0 candidate seed terminal

noncomputable def language :Language:={q |Incidence hn ht ha hR0 (pairFst q) (pairSnd q)}

theorem bounded_iff (q :List Bool):
    q∈boundedLanguage hn ht ha hR0 ↔q∈language hn ht ha hR0:=by
  constructor
  · rintro ⟨word,_,HM,HR⟩
    refine ⟨marker (pair q word),HM,?_⟩
    simpa only [nativeReachLanguage,Set.mem_ofPred_eq,reachQuery,leftLabel,rightLabel,pairFst_pair,pairSnd_pair]
      using HR
  · rintro ⟨terminal,HM,HR⟩
    refine ⟨label hn ht ha hR0 (pairFst q) terminal,
      label_length hn ht ha hR0 (pairFst q) terminal HR.2.1 HR.2.2.2.1,?_,?_⟩
    · simpa only [marker,pairSnd_pair,label_decode] using HM
    · simpa only [nativeReachLanguage,Set.mem_ofPred_eq,reachQuery,marker,leftLabel,rightLabel,
        pairFst_pair,pairSnd_pair,label_decode] using HR

theorem decider :SpaceDecider (language hn ht ha hR0):=
  (bounded_decider hn ht ha hR0).congr (Set.ext (bounded_iff hn ht ha hR0))

theorem mem_PSPACE :language hn ht ha hR0∈PSPACE:=(decider hn ht ha hR0).mem_PSPACE

end LeanCanny.Connectivity.IntegralMixedRoadmapAnchorIncidence

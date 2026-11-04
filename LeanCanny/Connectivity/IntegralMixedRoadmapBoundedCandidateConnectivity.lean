/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorGeometry
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateFilter
/-! # Native PSPACE decision for actual bounded candidate connectivity

Invalid candidate labels are rejected. The component relation uses the
original polynomial and an original-only radius, before any roadmap words
are chosen. This does not identify bounded and unbounded components.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapBoundedCandidateConnectivity
open Set LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open scoped Classical
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)

def original (q :List Bool):=pairFst q
def label (side :Bool) (q :List Bool):=
  if side then pairSnd (pairSnd q) else pairFst (pairSnd q)
def candidate (side :Bool) (q :List Bool):=pair (original q) (label side q)
def canonical (q :List Bool):=pair (original q) (pair (label false q) (label true q))
theorem candidate_FP (side :Bool):candidate side∈FP:=by cases side <;> polytime [candidate,original,label]
theorem canonical_FP :canonical∈FP:=by polytime [canonical,original,label]

noncomputable def language :Language:={q |
  ∃hA :AuxiliaryCandidateComponentCover.Good hn ht ha (original q) (label false q),
  ∃hB :AuxiliaryCandidateComponentCover.Good hn ht ha (original q) (label true q),
    IntegralMixedAuxiliaryCandidate.pointAt hn ht ha (original q) (label true q) (Classical.choose hB)∈
      connectedComponentIn (BoundedZeroSource.Bounded
        ((t (original q)).finitePolynomial (n (original q))) (R0 (original q)))
        (IntegralMixedAuxiliaryCandidate.pointAt hn ht ha (original q) (label false q) (Classical.choose hA))}

noncomputable def guardedLanguage :Language:={q |
  candidate false q∈IntegralMixedAuxiliaryCandidate.filteredLanguage hn ht ha ∧
  candidate true q∈IntegralMixedAuxiliaryCandidate.filteredLanguage hn ht ha ∧
  canonical q∈IntegralMixedRoadmapTwoAnchorCost.language hn ht ha hR0}

theorem guarded_decider :SpaceDecider (guardedLanguage hn ht ha hR0):=by
  have EA:=((IntegralMixedAuxiliaryCandidate.filtered_decider hn ht ha).precompose
    (candidate false) (candidate_FP false)).flagEvaluator
  have EB:=((IntegralMixedAuxiliaryCandidate.filtered_decider hn ht ha).precompose
    (candidate true) (candidate_FP true)).flagEvaluator
  have EC:=((IntegralMixedRoadmapTwoAnchorCost.decider hn ht ha hR0).precompose
    canonical canonical_FP).flagEvaluator
  apply (EA.andFlags (EB.andFlags EC)).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [guardedLanguage,Set.mem_ofPred_eq,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq]

theorem guarded_iff
    (hRadius :∀u,IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u) (q :List Bool):
    q∈guardedLanguage hn ht ha hR0 ↔q∈language hn ht ha (R0:=R0):=by
  constructor
  · rintro ⟨HA,HB,HC⟩
    have hA :AuxiliaryCandidateComponentCover.Good hn ht ha (original q) (label false q):=
      (IntegralMixedAuxiliaryCandidate.filtered_iff_pointAt_eval hn ht ha _ _).mp HA
    have hB :AuxiliaryCandidateComponentCover.Good hn ht ha (original q) (label true q):=
      (IntegralMixedAuxiliaryCandidate.filtered_iff_pointAt_eval hn ht ha _ _).mp HB
    exact ⟨hA,hB,(IntegralMixedRoadmapTwoAnchorGeometry.language_iff_component hn ht ha hR0
      (original q) (label false q) (label true q) hA hB (hRadius _)).mp HC⟩
  · rintro ⟨hA,hB,HC⟩
    exact ⟨(IntegralMixedAuxiliaryCandidate.filtered_iff_pointAt_eval hn ht ha _ _).mpr hA,
      (IntegralMixedAuxiliaryCandidate.filtered_iff_pointAt_eval hn ht ha _ _).mpr hB,
      (IntegralMixedRoadmapTwoAnchorGeometry.language_iff_component hn ht ha hR0
        (original q) (label false q) (label true q) hA hB (hRadius _)).mpr HC⟩

include hR0 in
theorem decider (hRadius :∀u,IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u):
    SpaceDecider (language hn ht ha (R0:=R0)):=
  (guarded_decider hn ht ha hR0).congr (Set.ext (guarded_iff hn ht ha hR0 hRadius))

include hR0 in
theorem mem_PSPACE (hRadius :∀u,IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u):
    language hn ht ha (R0:=R0)∈PSPACE:=(decider hn ht ha hR0 hRadius).mem_PSPACE

/-- An actual original-only radius gives an unconditional bounded-language result. -/
theorem candidate_radius_mem_PSPACE :
    language hn ht ha (R0:=IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha)∈PSPACE:=
  mem_PSPACE hn ht ha (IntegralMixedAuxiliaryCandidateRadius.radius_binary hn ht ha) (fun _=>le_rfl)

end LeanCanny.Connectivity.IntegralMixedRoadmapBoundedCandidateConnectivity

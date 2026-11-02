/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedAuxiliaryCandidateGraph
/-! # Total raw endpoint queries for the candidate graph

Savitch receives normalized fixed-width endpoints. The public language rejects
malformed endpoint lengths before accepting, preserving the raw graph query.
Adjacency and original-point filtering remain explicit decider premises.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedAuxiliaryCandidateGraph
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def querySource (q : List Bool) := pairFst (pairSnd q)
def queryTarget (q : List Bool) := pairSnd (pairSnd q)

def EndpointGuard {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (q : List Bool) : Prop :=
  (querySource q).length=IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (pairFst q) ∧
  (queryTarget q).length=IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (pairFst q)

noncomputable def normalizedSource {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (q : List Bool) :=
  IntegralMixedAuxiliaryCandidate.pad (IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (pairFst q)) (querySource q)

noncomputable def normalizedTarget {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (q : List Bool) :=
  IntegralMixedAuxiliaryCandidate.pad (IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (pairFst q)) (queryTarget q)

def reachLanguage {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (adjacent : List Bool → List Bool → List Bool → Prop) (allowed : List Bool → List Bool → Prop) : Language :=
  {q | EndpointGuard hn ht ha q ∧ ImplicitGraph.Reachable (edges adjacent (pairFst q))
    (vertices hn ht ha allowed (pairFst q)) (IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (pairFst q))
    (querySource q) (queryTarget q)}

theorem endpoint_guard_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    FPPred (EndpointGuard hn ht ha) :=
  (FPPred.eq (UnaryFn.length (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))
    ((IntegralMixedAuxiliaryCandidate.labelWidth_unary hn ht ha).comp pairFst_mem_FP)).and
  (FPPred.eq (UnaryFn.length (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))
    ((IntegralMixedAuxiliaryCandidate.labelWidth_unary hn ht ha).comp pairFst_mem_FP))

theorem normalizedSource_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    normalizedSource hn ht ha∈FP := IntegralMixedAuxiliaryCandidate.pad_FP
  ((IntegralMixedAuxiliaryCandidate.labelWidth_unary hn ht ha).comp pairFst_mem_FP)
  (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)

theorem normalizedTarget_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    normalizedTarget hn ht ha∈FP := IntegralMixedAuxiliaryCandidate.pad_FP
  ((IntegralMixedAuxiliaryCandidate.labelWidth_unary hn ht ha).comp pairFst_mem_FP)
  (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

theorem normalizedSource_eq {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : EndpointGuard hn ht ha q) : normalizedSource hn ht ha q=querySource q := by
  unfold normalizedSource IntegralMixedAuxiliaryCandidate.pad
  rw [←hq.1,List.take_length,Nat.sub_self,List.replicate_zero,List.append_nil]

theorem normalizedTarget_eq {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : EndpointGuard hn ht ha q) : normalizedTarget hn ht ha q=queryTarget q := by
  unfold normalizedTarget IntegralMixedAuxiliaryCandidate.pad
  rw [←hq.2,List.take_length,Nat.sub_self,List.replicate_zero,List.append_nil]

theorem reach_decider {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    {adjacent : List Bool → List Bool → List Bool → Prop} {allowed : List Bool → List Bool → Prop}
    (hE : SpaceDecider (edgeLanguage adjacent)) (hA : SpaceDecider (filterLanguage allowed)) :
    SpaceDecider (reachLanguage hn ht ha adjacent allowed) := by
  have hp := ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits)
  have hr := ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)
  have HE := (edge_computable hE).comp (.of_polyTime ((pairFst_mem_FP.comp hp).prod hr))
  have HV := (vertex_computable hn ht ha hA).comp (.of_polyTime
    ((pairFst_mem_FP.comp (ComputableTidilyInPolyTime.fst encBits encBits)).prod
      (ComputableTidilyInPolyTime.snd encBits encBits)))
  have HR := ImplicitGraph.reachable_computable
    (edge:=fun q => edges adjacent (pairFst q)) (valid:=fun q => vertices hn ht ha allowed (pairFst q))
    HE HV ((IntegralMixedAuxiliaryCandidate.labelWidth_unary hn ht ha).comp pairFst_mem_FP)
    (.of_polyTime (normalizedSource_FP hn ht ha)) (.of_polyTime (normalizedTarget_FP hn ht ha))
    (fun q => IntegralMixedAuxiliaryCandidate.pad_length _ _) (fun q => IntegralMixedAuxiliaryCandidate.pad_length _ _)
  have HG := ComputableTidilyInPolySpace.of_polyTime (endpoint_guard_FP hn ht ha).computable
  have HF := ComputableTidilyInPolySpace.of_polyTime
    (ComputableTidilyInPolyTime.const (encIn:=encBits) (encMid:=encBool) false)
  apply SpaceDecider.of_computable (HG.ite HR HF)
  intro q
  change EndpointGuard hn ht ha q ∧ ImplicitGraph.Reachable _ _ _ (querySource q) (queryTarget q) ↔
    (if decide (EndpointGuard hn ht ha q) then
      decide (ImplicitGraph.Reachable _ _ _ (normalizedSource hn ht ha q) (normalizedTarget hn ht ha q)) else false)=true
  by_cases h : EndpointGuard hn ht ha q
  · simp only [h,true_and,decide_true,ite_true,normalizedSource_eq hn ht ha q h,
      normalizedTarget_eq hn ht ha q h,decide_eq_true_eq]
  · simp only [h,false_and,decide_false,ite_false,Bool.false_eq_true]

theorem reach_mem_PSPACE {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    {adjacent : List Bool → List Bool → List Bool → Prop} {allowed : List Bool → List Bool → Prop}
    (hE : SpaceDecider (edgeLanguage adjacent)) (hA : SpaceDecider (filterLanguage allowed)) :
    reachLanguage hn ht ha adjacent allowed∈PSPACE := (reach_decider hn ht ha hE hA).mem_PSPACE

theorem reject_source_length {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (adjacent : List Bool → List Bool → List Bool → Prop) (allowed : List Bool → List Bool → Prop)
    (q : List Bool) (hq : (querySource q).length≠IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (pairFst q)) :
    q∉reachLanguage hn ht ha adjacent allowed := fun h => hq h.1.1
end LeanCanny.Connectivity.IntegralMixedAuxiliaryCandidateGraph

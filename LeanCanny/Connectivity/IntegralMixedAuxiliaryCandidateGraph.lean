/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateDecode
public import LeanCanny.Computation.ImplicitGraphPSPACE
/-! # Native implicit graphs on fixed-width auxiliary candidate labels

Candidate validity and width costs are discharged by original syntax. The
additional vertex filter and adjacency deciders are EXPLICIT premises. This
module does not identify the graph with connectivity of the original set.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedAuxiliaryCandidateGraph
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def edgeLanguage (adjacent : List Bool → List Bool → List Bool → Prop) : Language :=
  {q | adjacent (pairFst q) (pairFst (pairSnd q)) (pairSnd (pairSnd q))}

def filterLanguage (allowed : List Bool → List Bool → Prop) : Language :=
  {q | allowed (pairFst q) (pairSnd q)}

noncomputable def edges (adjacent : List Bool → List Bool → List Bool → Prop)
    (original u v : List Bool) := decide (adjacent original u v)

noncomputable def vertices {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (allowed : List Bool → List Bool → Prop) (original u : List Bool) :=
  decide (IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair original u) ∧ allowed original u)

private theorem inter_decider {L M : Language} (D : SpaceDecider L) (E : SpaceDecider M) :
    SpaceDecider (L∩M) := by
  have HF := ComputableInPolySpace.of_tidyPolyTime
    (ComputableTidilyInPolyTime.const (encIn:=encBits) (encMid:=encBool) false)
  apply SpaceDecider.of_computable (D.computable.ite E.computable HF)
  intro q
  by_cases h : q∈L <;> simp only [Set.mem_inter_iff,h,decide_true,decide_false,
    ite_true,ite_false,true_and,false_and,Bool.false_eq_true,decide_eq_true_eq]

theorem edge_computable {adjacent : List Bool → List Bool → List Bool → Prop}
    (hE : SpaceDecider (edgeLanguage adjacent)) :
    ComputableInPolySpace
      (fun p : List Bool × List Bool × List Bool => edges adjacent p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits)) encBool := by
  have hp := ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits)
  have hr := ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)
  have H := hE.computable.comp (.of_tidyPolyTime (pair_computable hp (pair_computable hr.fst' hr.snd')))
  exact H.congr (fun p => by simp only [edgeLanguage,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,edges])

theorem vertex_computable {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    {allowed : List Bool → List Bool → Prop} (hA : SpaceDecider (filterLanguage allowed)) :
    ComputableInPolySpace (fun p : List Bool × List Bool => vertices hn ht ha allowed p.1 p.2)
      (encPair encBits encBits) encBool := by
  have D := inter_decider (IntegralMixedAuxiliaryCandidate.decider hn ht ha) hA
  have H := D.computable.comp (.of_tidyPolyTime (pair_computable
    (ComputableTidilyInPolyTime.fst encBits encBits) (ComputableTidilyInPolyTime.snd encBits encBits)))
  exact H.congr (fun p => by simp only [vertices,Set.mem_inter_iff,filterLanguage,
    IntegralMixedAuxiliaryCandidate.language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair])

def connectedLanguage {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (adjacent : List Bool → List Bool → List Bool → Prop) (allowed : List Bool → List Bool → Prop) : Language :=
  {original | ImplicitGraph.Connected (edges adjacent original) (vertices hn ht ha allowed original)
    (IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)}

theorem connected_decider {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    {adjacent : List Bool → List Bool → List Bool → Prop} {allowed : List Bool → List Bool → Prop}
    (hE : SpaceDecider (edgeLanguage adjacent)) (hA : SpaceDecider (filterLanguage allowed)) :
    SpaceDecider (connectedLanguage hn ht ha adjacent allowed) := by
  apply SpaceDecider.of_computable (ImplicitGraph.connected_computable
    (edge_computable hE) (vertex_computable hn ht ha hA)
    (IntegralMixedAuxiliaryCandidate.labelWidth_unary hn ht ha))
  intro q
  simp only [connectedLanguage,Set.mem_ofPred_eq,decide_eq_true_eq]

theorem connected_mem_PSPACE {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    {adjacent : List Bool → List Bool → List Bool → Prop} {allowed : List Bool → List Bool → Prop}
    (hE : SpaceDecider (edgeLanguage adjacent)) (hA : SpaceDecider (filterLanguage allowed)) :
    connectedLanguage hn ht ha adjacent allowed∈PSPACE :=
  (connected_decider hn ht ha hE hA).mem_PSPACE
end LeanCanny.Connectivity.IntegralMixedAuxiliaryCandidateGraph

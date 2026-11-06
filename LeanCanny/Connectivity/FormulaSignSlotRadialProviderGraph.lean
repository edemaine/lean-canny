/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderEdge
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicSize
public import LeanCanny.Encoding.IntegralMixedRoadmapWordLabel
public import LeanCanny.Computation.ImplicitGraphPSPACE
/-! # One concrete bounded native graph for a fixed literal provider

Every accepted atomic vertex embeds at the provider polynomial width. Both
vertex validation and adjacency use the actual native predicates. The graph's
geometric component equivalence remains a separate theorem.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def width (c : List Bool):=2*FormulaSignSlotRadialProviderAtomic.providerVertexBudget c+2
theorem width_unary : UnaryFn (width):=
  ((UnaryFn.const 2).mul FormulaSignSlotRadialProviderAtomic.providerVertexBudget_unary).add (UnaryFn.const 2)

def vertex (z : List Bool):=IntegralMixedRoadmapWordLabel.decode (pairSnd z)
theorem vertex_FP : vertex∈FP:=mem_FP_comp pairSnd_mem_FP IntegralMixedRoadmapWordLabel.decode_FP

noncomputable def Valid (c r : List Bool):=FormulaSignSlotRadialProviderAtomic.provider (IntegralMixedRoadmapWordLabel.decode r)=c∧
  FormulaSignSlotRadialProviderAtomic.Valid (IntegralMixedRoadmapWordLabel.decode r)
noncomputable def validLanguage : Language:={z |Valid (pairFst z) (pairSnd z)}

theorem valid_decider : SpaceDecider (validLanguage):=by
  have EC:=SpaceFunction.ofFP _ (Brackets.stringEq_fppred
    (mem_FP_comp (f:=vertex) (g:=FormulaSignSlotRadialProviderAtomic.provider) vertex_FP FormulaSignSlotRadialProviderAtomic.provider_FP)
      pairFst_mem_FP).flag_mem_FP
  have EV:=(FormulaSignSlotRadialProviderAtomic.evaluator).precompose vertex vertex_FP
  apply (EC.andFlags EV).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [validLanguage,Valid,Set.mem_ofPred_eq,Function.comp_apply,vertex,List.cons.injEq,and_true,decide_eq_true_eq]

def edgePacket (z : List Bool):=pair (IntegralMixedRoadmapWordLabel.decode (pairFst (pairSnd z)))
  (IntegralMixedRoadmapWordLabel.decode (pairSnd (pairSnd z)))
theorem edgePacket_FP : edgePacket∈FP:=mem_FP_pair
  (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) IntegralMixedRoadmapWordLabel.decode_FP)
  (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) IntegralMixedRoadmapWordLabel.decode_FP)
noncomputable def edgeLanguage : Language:=edgePacket ⁻¹' FormulaSignSlotRadialProviderEdge.language
noncomputable def edges (_c a b : List Bool):=decide (FormulaSignSlotRadialProviderEdge.Adjacent
  (IntegralMixedRoadmapWordLabel.decode a) (IntegralMixedRoadmapWordLabel.decode b))
noncomputable def vertices (c r : List Bool):=decide (Valid c r)

theorem edge_computable : ComputableTidilyInPolySpace
    (fun p : List Bool×List Bool×List Bool=>edges p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) encBool :=by
  have HD:=(FormulaSignSlotRadialProviderEdge.decider).precompose edgePacket edgePacket_FP
  have hp:=ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits)
  have hr:=ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)
  have H:=HD.computable.comp (.of_polyTime (pair_computable hp (pair_computable hr.fst' hr.snd')))
  exact H.congr (fun p=>by simp only [Set.mem_preimage,edgePacket,pairFst_pair,pairSnd_pair,edges,FormulaSignSlotRadialProviderEdge.Adjacent])

theorem vertex_computable : ComputableTidilyInPolySpace
    (fun p : List Bool×List Bool=>vertices p.1 p.2)
    (encPair encBits encBits) encBool :=by
  have HD:=valid_decider
  have H:=HD.computable.comp (.of_polyTime (pair_computable
    (ComputableTidilyInPolyTime.fst encBits encBits) (ComputableTidilyInPolyTime.snd encBits encBits)))
  exact H.congr (fun p=>by simp only [validLanguage,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,vertices])

noncomputable def connectedLanguage : Language:={c |ImplicitGraph.Connected
  (edges c) (vertices c) (width c)}
theorem connected_decider : SpaceDecider (connectedLanguage):=by
  apply SpaceDecider.of_computable (ImplicitGraph.connected_computable
    (edge_computable) (vertex_computable) (width_unary))
  intro c
  simp only [connectedLanguage,Set.mem_ofPred_eq,decide_eq_true_eq]
theorem connected_mem_PSPACE : connectedLanguage∈PSPACE:=(connected_decider).mem_PSPACE

/-- All accepted vertices have literal representatives among the fixed-width labels. -/
theorem encode_vertex (c q : List Bool) (hq : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hc : FormulaSignSlotRadialProviderAtomic.provider q=c) :
    ∃r : List Bool,r.length=width c∧IntegralMixedRoadmapWordLabel.decode r=q∧Valid c r :=by
  let W:=FormulaSignSlotRadialProviderAtomic.providerVertexBudget c
  have HB : q.length≤W:=by
    simpa only [W,hc] using FormulaSignSlotRadialProviderAtomic.vertex_length_provider q hq
  refine ⟨IntegralMixedRoadmapWordLabel.encode W q,IntegralMixedRoadmapWordLabel.encode_length W q HB,
    IntegralMixedRoadmapWordLabel.decode_encode W q,?_⟩
  simpa only [Valid,IntegralMixedRoadmapWordLabel.decode_encode] using And.intro hc hq

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph

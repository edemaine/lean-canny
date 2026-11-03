/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapEdge
public import LeanCanny.Encoding.IntegralMixedRoadmapWordLabel
public import LeanCanny.Computation.ImplicitGraphPSPACE
/-! # One concrete bounded native graph for a fixed original candidate

Every accepted atomic vertex embeds at the original polynomial width. Both
vertex validation and adjacency use the actual native predicates. The graph's
geometric soundness/completeness and outer stabilization remain separate.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)

noncomputable def width (c : List Bool):=2*IntegralMixedRoadmapAtomic.byteBudget hn ht ha hR0 (pairFst c)+2
theorem width_unary : UnaryFn (width hn ht ha hR0):=
  ((UnaryFn.const 2).mul ((IntegralMixedRoadmapAtomic.byteBudget_unary hn ht ha hR0).comp pairFst_mem_FP)).add (UnaryFn.const 2)

def vertex (z : List Bool):=IntegralMixedRoadmapWordLabel.decode (pairSnd z)
theorem vertex_FP : vertex∈FP:=mem_FP_comp pairSnd_mem_FP IntegralMixedRoadmapWordLabel.decode_FP

noncomputable def Valid (c r : List Bool):=IntegralMixedRoadmapAtomic.candidate (IntegralMixedRoadmapWordLabel.decode r)=c∧
  IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapWordLabel.decode r)
noncomputable def validLanguage : Language:={z |Valid hn ht ha hR0 (pairFst z) (pairSnd z)}

theorem valid_decider : SpaceDecider (validLanguage hn ht ha hR0):=by
  have EC:=SpaceFunction.ofFP _ (Brackets.stringEq_fppred
    (mem_FP_comp (f:=vertex) (g:=IntegralMixedRoadmapAtomic.candidate) vertex_FP IntegralMixedRoadmapAtomic.candidate_FP)
      pairFst_mem_FP).flag_mem_FP
  have EV:=(IntegralMixedRoadmapAtomic.evaluator hn ht ha hR0).precompose vertex vertex_FP
  apply (EC.andFlags EV).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [validLanguage,Valid,Set.mem_ofPred_eq,Function.comp_apply,vertex,List.cons.injEq,and_true,decide_eq_true_eq]

def edgePacket (z : List Bool):=pair (IntegralMixedRoadmapWordLabel.decode (pairFst (pairSnd z)))
  (IntegralMixedRoadmapWordLabel.decode (pairSnd (pairSnd z)))
theorem edgePacket_FP : edgePacket∈FP:=mem_FP_pair
  (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) IntegralMixedRoadmapWordLabel.decode_FP)
  (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) IntegralMixedRoadmapWordLabel.decode_FP)
noncomputable def edgeLanguage : Language:=edgePacket ⁻¹' IntegralMixedRoadmapEdge.language hn ht ha hR0
noncomputable def edges (_c a b : List Bool):=decide (IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0
  (IntegralMixedRoadmapWordLabel.decode a) (IntegralMixedRoadmapWordLabel.decode b))
noncomputable def vertices (c r : List Bool):=decide (Valid hn ht ha hR0 c r)

theorem edge_computable : ComputableTidilyInPolySpace
    (fun p : List Bool×List Bool×List Bool=>edges hn ht ha hR0 p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) encBool :=by
  have HD:=(IntegralMixedRoadmapEdge.decider hn ht ha hR0).precompose edgePacket edgePacket_FP
  have hp:=ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits)
  have hr:=ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)
  have H:=HD.computable.comp (.of_polyTime (pair_computable hp (pair_computable hr.fst' hr.snd')))
  exact H.congr (fun p=>by simp only [Set.mem_preimage,edgePacket,pairFst_pair,pairSnd_pair,edges,IntegralMixedRoadmapEdge.Adjacent])

theorem vertex_computable : ComputableTidilyInPolySpace
    (fun p : List Bool×List Bool=>vertices hn ht ha hR0 p.1 p.2)
    (encPair encBits encBits) encBool :=by
  have HD:=valid_decider hn ht ha hR0
  have H:=HD.computable.comp (.of_polyTime (pair_computable
    (ComputableTidilyInPolyTime.fst encBits encBits) (ComputableTidilyInPolyTime.snd encBits encBits)))
  exact H.congr (fun p=>by simp only [validLanguage,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,vertices])

noncomputable def connectedLanguage : Language:={c |ImplicitGraph.Connected
  (edges hn ht ha hR0 c) (vertices hn ht ha hR0 c) (width hn ht ha hR0 c)}
theorem connected_decider : SpaceDecider (connectedLanguage hn ht ha hR0):=by
  apply SpaceDecider.of_computable (ImplicitGraph.connected_computable
    (edge_computable hn ht ha hR0) (vertex_computable hn ht ha hR0) (width_unary hn ht ha hR0))
  intro c
  simp only [connectedLanguage,Set.mem_ofPred_eq,decide_eq_true_eq]
theorem connected_mem_PSPACE : connectedLanguage hn ht ha hR0∈PSPACE:=(connected_decider hn ht ha hR0).mem_PSPACE

/-- All accepted vertices have literal representatives among the fixed-width labels. -/
theorem encode_vertex (c q : List Bool) (hq : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc : IntegralMixedRoadmapAtomic.candidate q=c) :
    ∃r : List Bool,r.length=width hn ht ha hR0 c∧IntegralMixedRoadmapWordLabel.decode r=q∧Valid hn ht ha hR0 c r :=by
  let W:=IntegralMixedRoadmapAtomic.byteBudget hn ht ha hR0 (pairFst c)
  have HO : IntegralMixedRoadmapAtomic.original q=pairFst c:=congrArg pairFst hc
  have HB : q.length≤W:=by simpa only [W,HO] using IntegralMixedRoadmapAtomic.byte_bound hn ht ha hR0 q hq
  refine ⟨IntegralMixedRoadmapWordLabel.encode W q,IntegralMixedRoadmapWordLabel.encode_length W q HB,
    IntegralMixedRoadmapWordLabel.decode_encode W q,?_⟩
  simpa only [Valid,IntegralMixedRoadmapWordLabel.decode_encode] using And.intro hc hq

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph

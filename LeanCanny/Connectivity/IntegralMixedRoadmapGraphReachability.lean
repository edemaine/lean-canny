/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapGraph
/-! # Native point-to-point reachability in the actual bounded roadmap graph

The input contains a candidate and two literal fixed-width graph labels.
Wrong lengths are rejected. Both endpoints and all intermediates are checked
by the original native atomic predicate; no adjacency-cost premise is supplied.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def leftLabel (q : List Bool):=pairFst (pairSnd q)
def rightLabel (q : List Bool):=pairSnd (pairSnd q)

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)

noncomputable def reachLanguage : Language:={q |
  (leftLabel q).length=width hn ht ha hR0 (pairFst q)∧
  (rightLabel q).length=width hn ht ha hR0 (pairFst q)∧
  ImplicitGraph.Reachable (edges hn ht ha hR0 (pairFst q)) (vertices hn ht ha hR0 (pairFst q))
    (width hn ht ha hR0 (pairFst q)) (leftLabel q) (rightLabel q)}

theorem reach_decider : SpaceDecider (reachLanguage hn ht ha hR0):=by
  have hp:=ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits)
  have hr:=ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)
  have he:=(edge_computable hn ht ha hR0).comp
    (.of_polyTime (((FP.computable pairFst_mem_FP).comp hp).prod hr))
  have hq:=ComputableTidilyInPolyTime.fst encBits encBits
  have ht':=ComputableTidilyInPolyTime.snd encBits encBits
  have hv:=(vertex_computable hn ht ha hR0).comp
    (.of_polyTime (((FP.computable pairFst_mem_FP).comp hq).prod ht'))
  have hw : UnaryFn (fun q=>width hn ht ha hR0 (pairFst q)):=(width_unary hn ht ha hR0).comp pairFst_mem_FP
  have hl : leftLabel∈FP:=mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hd : rightLabel∈FP:=mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hs:=ImplicitGraph.word_computable hw (BinaryFn.fromBits hl)
  have ht'' :=ImplicitGraph.word_computable hw (BinaryFn.fromBits hd)
  have G:=ImplicitGraph.reachable_computable (edge:=fun q=>edges hn ht ha hR0 (pairFst q))
    (valid:=fun q=>vertices hn ht ha hR0 (pairFst q)) he hv hw (.of_polyTime hs) (.of_polyTime ht'')
    (fun _=>ImplicitGraph.length_word _ _) (fun _=>ImplicitGraph.length_word _ _)
  have HG:=(FPPred.eq (UnaryFn.length hl) hw).and (FPPred.eq (UnaryFn.length hd) hw)
  have F : ComputableTidilyInPolySpace (fun _ : List Bool=>false) encBits encBool:=
    .of_polyTime (ComputableTidilyInPolyTime.const false)
  apply SpaceDecider.of_computable ((ComputableTidilyInPolySpace.of_polyTime HG.computable).ite G F)
  intro q
  by_cases HW : (leftLabel q).length=width hn ht ha hR0 (pairFst q)∧
      (rightLabel q).length=width hn ht ha hR0 (pairFst q)
  · have HL : ImplicitGraph.word (width hn ht ha hR0 (pairFst q)) (Nat.fromBitsLE (leftLabel q))=leftLabel q:=by
      rw [←HW.1,ImplicitGraph.word_fromBitsLE]
    have HR : ImplicitGraph.word (width hn ht ha hR0 (pairFst q)) (Nat.fromBitsLE (rightLabel q))=rightLabel q:=by
      rw [←HW.2,ImplicitGraph.word_fromBitsLE]
    simp only [reachLanguage,Set.mem_ofPred_eq,HW.1,HW.2,true_and,decide_true,ite_true,decide_eq_true_eq,HL,HR]
  · simp only [reachLanguage,Set.mem_ofPred_eq,HW,decide_false,ite_false,Bool.false_eq_true]
    tauto

theorem reach_mem_PSPACE : reachLanguage hn ht ha hR0∈PSPACE:=(reach_decider hn ht ha hR0).mem_PSPACE

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
/-! # Native point-to-point reachability in the actual bounded roadmap graph

The input contains a candidate and two literal fixed-width graph labels.
Wrong lengths are rejected. Both endpoints and all intermediates are checked
by the original native atomic predicate; no adjacency-cost premise is supplied.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def leftLabel (q : List Bool):=pairFst (pairSnd q)
def rightLabel (q : List Bool):=pairSnd (pairSnd q)

noncomputable def reachLanguage : Language:={q |
  (leftLabel q).length=width (pairFst q)∧
  (rightLabel q).length=width (pairFst q)∧
  ImplicitGraph.Reachable (edges (pairFst q)) (vertices (pairFst q))
    (width (pairFst q)) (leftLabel q) (rightLabel q)}

theorem reach_decider : SpaceDecider (reachLanguage):=by
  have hp:=ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits)
  have hr:=ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)
  have he:=(edge_computable).comp
    (.of_polyTime (((FP.computable pairFst_mem_FP).comp hp).prod hr))
  have hq:=ComputableTidilyInPolyTime.fst encBits encBits
  have ht':=ComputableTidilyInPolyTime.snd encBits encBits
  have hv:=(vertex_computable).comp
    (.of_polyTime (((FP.computable pairFst_mem_FP).comp hq).prod ht'))
  have hw : UnaryFn (fun q=>width (pairFst q)):=(width_unary).comp pairFst_mem_FP
  have hl : leftLabel∈FP:=mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hd : rightLabel∈FP:=mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hs:=ImplicitGraph.word_computable hw (BinaryFn.fromBits hl)
  have ht'' :=ImplicitGraph.word_computable hw (BinaryFn.fromBits hd)
  have G:=ImplicitGraph.reachable_computable (edge:=fun q=>edges (pairFst q))
    (valid:=fun q=>vertices (pairFst q)) he hv hw (.of_polyTime hs) (.of_polyTime ht'')
    (fun _=>ImplicitGraph.length_word _ _) (fun _=>ImplicitGraph.length_word _ _)
  have HG:=(FPPred.eq (UnaryFn.length hl) hw).and (FPPred.eq (UnaryFn.length hd) hw)
  have F : ComputableTidilyInPolySpace (fun _ : List Bool=>false) encBits encBool:=
    .of_polyTime (ComputableTidilyInPolyTime.const false)
  apply SpaceDecider.of_computable ((ComputableTidilyInPolySpace.of_polyTime HG.computable).ite G F)
  intro q
  by_cases HW : (leftLabel q).length=width (pairFst q)∧
      (rightLabel q).length=width (pairFst q)
  · have HL : ImplicitGraph.word (width (pairFst q)) (Nat.fromBitsLE (leftLabel q))=leftLabel q:=by
      rw [←HW.1,ImplicitGraph.word_fromBitsLE]
    have HR : ImplicitGraph.word (width (pairFst q)) (Nat.fromBitsLE (rightLabel q))=rightLabel q:=by
      rw [←HW.2,ImplicitGraph.word_fromBitsLE]
    simp only [reachLanguage,Set.mem_ofPred_eq,HW.1,HW.2,true_and,decide_true,ite_true,decide_eq_true_eq,HL,HR]
  · simp only [reachLanguage,Set.mem_ofPred_eq,HW,decide_false,ite_false,Bool.false_eq_true]
    tauto

theorem reach_mem_PSPACE : reachLanguage∈PSPACE:=(reach_decider).mem_PSPACE

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeTest
public import LeanCanny.Encoding.FixedWidthNatVectorFP
/-! # Bounded native search over ordinary bad-probe hints

Four fixed-width blocks encode tag, coordinate, factor choice and degree.
Each prepared root gets its own complete word. Rejection of this bounded
search is in PSPACE. Identifying it with ordinary bad-value avoidance still
requires the geometric soundness and completeness bridges.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSearch
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)

noncomputable def blockWidth (base : List Bool):=
  IntegralMixedRoadmapBadProbeTest.width hn ht ha hR (pair base [])+
    IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hR (pair base [])+2
theorem blockWidth_unary : UnaryFn (blockWidth hn ht ha hR):=
  (((IntegralMixedRoadmapBadProbeTest.width_unary hn ht ha hR).comp
    (mem_FP_pair id_mem_FP (constFn_mem_FP []))).add
    ((IntegralMixedRoadmapBadProbeTest.dimension_unary hn ht ha hR).comp
      (mem_FP_pair id_mem_FP (constFn_mem_FP [])))).add (UnaryFn.const 2)
noncomputable def hintWidth (base : List Bool):=4*blockWidth hn ht ha hR base
theorem hintWidth_unary : UnaryFn (hintWidth hn ht ha hR):=
  (UnaryFn.const 4).mul (blockWidth_unary hn ht ha hR)
noncomputable def block (i : ℕ) (z : List Bool):=
  ((pairSnd z).drop (i*blockWidth hn ht ha hR (pairFst z))).take
    (blockWidth hn ht ha hR (pairFst z))
theorem block_FP (i : ℕ) : block hn ht ha hR i∈FP:=
  take_mem_FP (drop_mem_FP pairSnd_mem_FP ((UnaryFn.const i).mul
    ((blockWidth_unary hn ht ha hR).comp pairFst_mem_FP)))
    ((blockWidth_unary hn ht ha hR).comp pairFst_mem_FP)
noncomputable def hintPacket (z : List Bool):=pair (pairFst z)
  (WordList.encode [block hn ht ha hR 0 z,block hn ht ha hR 1 z,
    block hn ht ha hR 2 z,block hn ht ha hR 3 z])
theorem hintPacket_FP : hintPacket hn ht ha hR∈FP:=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair (block_FP hn ht ha hR 0)
    (mem_FP_pair (block_FP hn ht ha hR 1) (mem_FP_pair (block_FP hn ht ha hR 2)
      (mem_FP_pair (block_FP hn ht ha hR 3) (constFn_mem_FP [])))))

theorem field_hintPacket (base bits : List Bool) (i : ℕ) (hi : i<4) :
    IntegralMixedRoadmapBadProbePacket.field i (hintPacket hn ht ha hR (pair base bits))=
      (bits.drop (i*blockWidth hn ht ha hR base)).take (blockWidth hn ht ha hR base) :=by
  interval_cases i <;> simp only [IntegralMixedRoadmapBadProbePacket.field,hintPacket,
    pairSnd_pair,pairFst_pair,WordList.get_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,block]

theorem encode_fields (base : List Bool) (e : ℕ→ℕ)
    (he : ∀i<4,e i<2^blockWidth hn ht ha hR base) (i : ℕ) (hi : i<4) :
    Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i
      (hintPacket hn ht ha hR (pair base
        (FixedWidthNatVector.encode 4 (blockWidth hn ht ha hR base) e))))=e i :=by
  rw [field_hintPacket hn ht ha hR _ _ i hi]
  exact FixedWidthNatVector.decode_block _ _ _ i hi (he i hi)

theorem ordinary_fields_fit (base : List Bool) (tag j choice degree : ℕ)
    (htg : tag<3)
    (hj : j<IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hR (pair base [])+1)
    (hc : choice≤2^IntegralMixedRoadmapBadProbeTest.width hn ht ha hR (pair base []))
    (hd : degree≤2^IntegralMixedRoadmapBadProbeTest.width hn ht ha hR (pair base [])) :
    tag<2^blockWidth hn ht ha hR base ∧ j<2^blockWidth hn ht ha hR base ∧
      choice<2^blockWidth hn ht ha hR base ∧ degree<2^blockWidth hn ht ha hR base :=by
  let B:=IntegralMixedRoadmapBadProbeTest.width hn ht ha hR (pair base [])
  let d:=IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hR (pair base [])
  have HB : B+1≤blockWidth hn ht ha hR base:=by dsimp [blockWidth,B];omega
  have HD : d≤blockWidth hn ht ha hR base:=by dsimp [blockWidth,d];omega
  have HT : 2≤blockWidth hn ht ha hR base:=by dsimp [blockWidth];omega
  have HP : 2^B<2^(B+1):=by rw [Nat.pow_succ];have :=Nat.two_pow_pos B;omega
  have Hcap : 2^B<2^blockWidth hn ht ha hR base:=
    HP.trans_le (Nat.pow_le_pow_right (by decide) HB)
  refine ⟨htg.trans_le ?_,?_,hc.trans_lt Hcap,hd.trans_lt Hcap⟩
  · exact (show 3≤2^2 by decide).trans (Nat.pow_le_pow_right (by decide) HT)
  · exact (show j≤d by dsimp [d];omega).trans_lt
      ((show d<2^d from Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_right (by decide) HD))

noncomputable def HasBadProbe (base : List Bool):=∃bits : List Bool,
  bits.length=hintWidth hn ht ha hR base ∧
    IntegralMixedRoadmapBadProbeTest.HasWitness hn ht ha hR (hintPacket hn ht ha hR (pair base bits))
noncomputable def NoBadProbe (base : List Bool):=¬HasBadProbe hn ht ha hR base

theorem hasBadProbe_evaluator : SpaceFunction (fun base=>[decide (HasBadProbe hn ht ha hR base)]):=by
  have E:=(IntegralMixedRoadmapBadProbeTest.hasWitness_evaluator hn ht ha hR).precompose _
    (hintPacket_FP hn ht ha hR)
  exact (E.exists_words (hintWidth_unary hn ht ha hR)).congr (funext fun base=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [HasBadProbe,List.cons.injEq,and_true,decide_eq_true_eq,Function.comp_apply])

theorem noBadProbe_evaluator : SpaceFunction (fun base=>[decide (NoBadProbe hn ht ha hR base)]):=by
  exact ((hasBadProbe_evaluator hn ht ha hR).postcompose _
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP).congr (funext fun base=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [NoBadProbe,id_eq,List.cons.injEq,and_true,decide_eq_true_eq])

noncomputable def language : Language:={base | NoBadProbe hn ht ha hR base}
theorem decider : SpaceDecider (language hn ht ha hR):=by
  apply (noBadProbe_evaluator hn ht ha hR).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro base
  simp only [language,List.cons.injEq,and_true,Set.mem_ofPred_eq,decide_eq_true_eq]
theorem mem_PSPACE : language hn ht ha hR∈PSPACE:=(decider hn ht ha hR).mem_PSPACE

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSearch

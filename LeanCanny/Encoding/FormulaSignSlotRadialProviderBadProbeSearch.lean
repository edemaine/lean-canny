/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeTest
public import LeanCanny.Encoding.FixedWidthNatVectorFP
/-! # Bounded native search over ordinary bad-probe hints

Four fixed-width blocks encode tag, coordinate, factor choice and degree.
Each prepared root gets its own complete word. Rejection of this bounded
search is in PSPACE. Identifying it with ordinary bad-value avoidance still
requires the geometric soundness and completeness bridges.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeSearch
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable def blockWidth (base : List Bool):=
  FormulaSignSlotRadialProviderBadProbeTest.width (pair base [])+
    FormulaSignSlotRadialProviderBadProbeTest.dimension (pair base [])+2
theorem blockWidth_unary : UnaryFn (blockWidth):=
  (((FormulaSignSlotRadialProviderBadProbeTest.width_unary).comp
    (mem_FP_pair id_mem_FP (constFn_mem_FP []))).add
    ((FormulaSignSlotRadialProviderBadProbeTest.dimension_unary).comp
      (mem_FP_pair id_mem_FP (constFn_mem_FP [])))).add (UnaryFn.const 2)
noncomputable def hintWidth (base : List Bool):=4*blockWidth base
theorem hintWidth_unary : UnaryFn (hintWidth):=
  (UnaryFn.const 4).mul (blockWidth_unary)
noncomputable def block (i : ℕ) (z : List Bool):=
  ((pairSnd z).drop (i*blockWidth (pairFst z))).take
    (blockWidth (pairFst z))
theorem block_FP (i : ℕ) : block i∈FP:=
  take_mem_FP (drop_mem_FP pairSnd_mem_FP ((UnaryFn.const i).mul
    ((blockWidth_unary).comp pairFst_mem_FP)))
    ((blockWidth_unary).comp pairFst_mem_FP)
noncomputable def hintPacket (z : List Bool):=pair (pairFst z)
  (WordList.encode [block 0 z,block 1 z,
    block 2 z,block 3 z])
theorem hintPacket_FP : hintPacket∈FP:=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair (block_FP 0)
    (mem_FP_pair (block_FP 1) (mem_FP_pair (block_FP 2)
      (mem_FP_pair (block_FP 3) (constFn_mem_FP [])))))

theorem field_hintPacket (base bits : List Bool) (i : ℕ) (hi : i<4) :
    IntegralMixedRoadmapBadProbePacket.field i (hintPacket (pair base bits))=
      (bits.drop (i*blockWidth base)).take (blockWidth base) :=by
  interval_cases i <;> simp only [IntegralMixedRoadmapBadProbePacket.field,hintPacket,
    pairSnd_pair,pairFst_pair,WordList.get_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,block]

theorem encode_fields (base : List Bool) (e : ℕ→ℕ)
    (he : ∀i<4,e i<2^blockWidth base) (i : ℕ) (hi : i<4) :
    Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i
      (hintPacket (pair base
        (FixedWidthNatVector.encode 4 (blockWidth base) e))))=e i :=by
  rw [field_hintPacket _ _ i hi]
  exact FixedWidthNatVector.decode_block _ _ _ i hi (he i hi)

theorem ordinary_fields_fit (base : List Bool) (tag j choice degree : ℕ)
    (htg : tag<3)
    (hj : j<FormulaSignSlotRadialProviderBadProbeTest.dimension (pair base [])+1)
    (hc : choice≤2^FormulaSignSlotRadialProviderBadProbeTest.width (pair base []))
    (hd : degree≤2^FormulaSignSlotRadialProviderBadProbeTest.width (pair base [])) :
    tag<2^blockWidth base ∧ j<2^blockWidth base ∧
      choice<2^blockWidth base ∧ degree<2^blockWidth base :=by
  let B:=FormulaSignSlotRadialProviderBadProbeTest.width (pair base [])
  let d:=FormulaSignSlotRadialProviderBadProbeTest.dimension (pair base [])
  have HB : B+1≤blockWidth base:=by dsimp [blockWidth,B];omega
  have HD : d≤blockWidth base:=by dsimp [blockWidth,d];omega
  have HT : 2≤blockWidth base:=by dsimp [blockWidth];omega
  have HP : 2^B<2^(B+1):=by rw [Nat.pow_succ];have :=Nat.two_pow_pos B;omega
  have Hcap : 2^B<2^blockWidth base:=
    HP.trans_le (Nat.pow_le_pow_right (by decide) HB)
  refine ⟨htg.trans_le ?_,?_,hc.trans_lt Hcap,hd.trans_lt Hcap⟩
  · exact (show 3≤2^2 by decide).trans (Nat.pow_le_pow_right (by decide) HT)
  · exact (show j≤d by dsimp [d];omega).trans_lt
      ((show d<2^d from Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_right (by decide) HD))

noncomputable def HasBadProbe (base : List Bool):=∃bits : List Bool,
  bits.length=hintWidth base ∧
    FormulaSignSlotRadialProviderBadProbeTest.HasWitness (hintPacket (pair base bits))
noncomputable def NoBadProbe (base : List Bool):=¬HasBadProbe base

theorem hasBadProbe_evaluator : SpaceFunction (fun base=>[decide (HasBadProbe base)]):=by
  have E:=(FormulaSignSlotRadialProviderBadProbeTest.hasWitness_evaluator).precompose _
    (hintPacket_FP)
  exact (E.exists_words (hintWidth_unary)).congr (funext fun base=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [HasBadProbe,List.cons.injEq,and_true,decide_eq_true_eq,Function.comp_apply])

theorem noBadProbe_evaluator : SpaceFunction (fun base=>[decide (NoBadProbe base)]):=by
  exact ((hasBadProbe_evaluator).postcompose _
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP).congr (funext fun base=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [NoBadProbe,id_eq,List.cons.injEq,and_true,decide_eq_true_eq])

noncomputable def language : Language:={base | NoBadProbe base}
theorem decider : SpaceDecider (language):=by
  apply (noBadProbe_evaluator).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro base
  simp only [language,List.cons.injEq,and_true,Set.mem_ofPred_eq,decide_eq_true_eq]
theorem mem_PSPACE : language∈PSPACE:=(decider).mem_PSPACE

end LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeSearch

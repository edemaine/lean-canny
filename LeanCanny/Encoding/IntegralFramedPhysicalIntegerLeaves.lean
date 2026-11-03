/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalUnivariateSpace
public import LeanCanny.Algebra.IntegralMixedDenominatorNative
public import LeanCanny.Computation.SpaceFunctionQuantifiers
/-! # Every original integer leaf at the same full physical vertex

Only the chronological birth is selected in the datum. All tests share the
literal full sampler context and vertex; the scan checks the original
untruncated polynomial rather than its padded sampler equation.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalIntegerLeaves
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
local notation "S"=>IntegralFramedPhysicalSquare.input P D H L F C hs key hpos

noncomputable def coordinate (c d : List Bool) : Fin ((family P D H).birth (key c)) :=
  ⟨(family P D H).birth (key c)-1-Nat.fromBitsLE d,by have HP:=hpos c; omega⟩

include hpos in
theorem coordinate_unary (a : Access P) (hk : key∈FP) :
    UnaryFn (IntegralFramedPhysicalUnivariateTest.selected P D H key (coordinate P D H key hpos)) := by
  have HC : UnaryFn (fun q=>(family P D H).birth (key (pairFst q))) :=
    ((IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp (mem_FP_comp pairFst_mem_FP hk))
  have HB : BinaryFn (IntegralFramedPhysicalUnivariateTest.selected P D H key (coordinate P D H key hpos)) :=
    ((BinaryFn.ofUnary HC).sub (BinaryFn.const 1)).sub (BinaryFn.fromBits pairSnd_mem_FP)
  exact IntegralMixedDenominatorScriptBits.binary_bounded_unary HB HC (fun q=>by
    change _-1-_≤_
    omega)

variable (Q : IntegerPolynomialRootQueriesBits.Source) (N : List Bool→ℕ)
noncomputable def value :=IntegralFramedPhysicalUnivariateTest.value P D H L F C hs key hpos
  (coordinate P D H key hpos) Q

attribute [local irreducible] value IntegralFramedPhysicalUnivariateTest.value

def probe (z : List Bool) :=pair (pair (pairFst (pairFst z)) (pairSnd (pairFst z))) (BinaryNatCode.encode (pairSnd z).length)
theorem probe_FP : probe∈FP :=mem_FP_pair
  (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))
  (BinaryFn.ofUnary (UnaryFn.length pairSnd_mem_FP)).bits_mem_FP

noncomputable def holds (q : List Bool) : Prop := ∀i<N (pairFst q),
  value P D H L F C hs key hpos Q (probe (pair q (List.replicate i true)))=InfinitesimalSign.encode 0
noncomputable def language : Language := {q |SquareSampleCompleteVertices.Valid S (pairFst q) (pairSnd q) ∧
  N (pairFst q)≤(family P D H).birth (key (pairFst q)) ∧ holds P D H L F C hs key hpos Q N q}

theorem holds_iff (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    holds P D H L F C hs key hpos Q N (pair c w) ↔ ∀i<N c,
      (Q.polynomial (pair c (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ)
        (IntegralFramedPhysicalSquare.point P D H L F C hs key hpos c w hv
          (coordinate P D H key hpos c (BinaryNatCode.encode i)))=0 := by
  have E (i : ℕ):=IntegralFramedPhysicalUnivariateTest.packet P D H L F C hs key hpos
    (coordinate P D H key hpos) Q c w (BinaryNatCode.encode i) hv
  simp only [holds,probe,pairFst_pair,pairSnd_pair,List.length_replicate,value]
  simp_rw [E,SquareSampleTestSign.encode_eq_iff,sign_eq_zero_iff]

theorem coordinate_packet (c : List Bool) (i : ℕ) :
    (coordinate P D H key hpos c (BinaryNatCode.encode i)).val=(family P D H).birth (key c)-1-i :=by
  simp only [coordinate,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem accepted_roots (q : List Bool) (hq : q∈language P D H L F C hs key hpos Q N) :
    ∃hv : SquareSampleCompleteVertices.Valid S (pairFst q) (pairSnd q),
      N (pairFst q)≤(family P D H).birth (key (pairFst q)) ∧
      ∀i<N (pairFst q),(Q.polynomial (pair (pairFst q) (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ)
        (IntegralFramedPhysicalSquare.point P D H L F C hs key hpos (pairFst q) (pairSnd q) hv
          (coordinate P D H key hpos (pairFst q) (BinaryNatCode.encode i)))=0 :=by
  obtain ⟨hv,hcount,hroots⟩:=hq
  refine ⟨hv,hcount,?_⟩
  apply (holds_iff P D H L F C hs key hpos Q N (pairFst q) (pairSnd q) hv).mp
  simpa only [holds,probe,pairFst_pair,pairSnd_pair] using hroots

variable (a : Access P) (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
  (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
  (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
  (nc : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
  (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew nc)
  (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hk : key∈FP)
  (hQ : IntegerPolynomialRootQueriesBits.Access Q) (hN : UnaryFn N)
  (ER : SpaceFunction (SquareSampleInput.rowCoefficient
    (IntegralFramedPhysicalSquare.input P D H L F C hs key hpos)))

include a ht hr hb hL hF hC hk hQ ER in
theorem value_evaluator : SpaceFunction (value P D H L F C hs key hpos Q) :=by
  unfold value
  exact IntegralFramedPhysicalUnivariateTest.evaluator P a D H T ht hr key hk (coordinate P D H key hpos)
    (coordinate_unary P D H key hpos a hk) Hnew nc hb hL hF hC hs Q hQ hpos ER

include a ht hr hb hL hF hC hk hQ hN ER in
theorem holds_evaluator : SpaceFunction (fun q=>[decide (holds P D H L F C hs key hpos Q N q)]) := by
  have E:=((value_evaluator P D H L F C hs key hpos Q a T ht hr Hnew nc hb hL hF hC hk hQ ER).precompose
    probe probe_FP).postcompose (fun z=>[decide (z=InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  exact (E.forall_unary (hN.comp pairFst_mem_FP)).congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [holds,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq])

include a ht hr hb hL hF hC hk hQ hN ER in
theorem decider : SpaceDecider (language P D H L F C hs key hpos Q N) := by
  have HA:=IntegralFramedPhysicalSquare.access P a D H T ht hr L F C hs hL hF hC key hk hpos ER
  have EV:=(SquareSampleCompleteVertices.decider HA).flagEvaluator
  have HC : UnaryFn (fun q=>(family P D H).birth (key (pairFst q))) :=
    (IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp (mem_FP_comp pairFst_mem_FP hk)
  have EP:=((BinaryFn.ofUnary (hN.comp pairFst_mem_FP)).le (BinaryFn.ofUnary HC)).flag_mem_FP
  have EG:=holds_evaluator P D H L F C hs key hpos Q N a T ht hr Hnew nc hb hL hF hC hk hQ hN ER
  apply (EV.andFlags ((SpaceFunction.ofFP _ EP).andFlags EG)).decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]
end LeanCanny.Encoding.IntegralFramedPhysicalIntegerLeaves

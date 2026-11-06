/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitValueTest
/-! # The actual VALUE interval is decided on the sampler's unchanged tuple

The finite outer search checks every coordinate selection and every lower
coefficient before applying the native two-moment interval decision.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitValueInterval
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F"=>FormulaSignSlotRadialJointStratumSampler.input
local notation "env"=>FormulaSignSlotRadialImplicitSourceTest.env
local notation "payload"=>FormulaSignSlotRadialImplicitValueSelection.packet
local notation "family"=>FormulaSignSlotRadialImplicitValueSelection.family
local notation "order"=>FormulaSignSlotRadialImplicitValueSelection.order
local notation "original"=>FormulaSignSlotRadialImplicitValueSelection.original
local notation "ctx"=>FormulaSignSlotRadialImplicitValueSelection.context

private theorem flag_eq {P Q:List Bool→Prop} (h:∀z,P z↔Q z)
    (E:SpaceFunction (fun z=>[decide (P z)])):SpaceFunction (fun z=>[decide (Q z)]):=
  E.congr (funext fun z=>congrArg List.singleton (Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using h z)))

def lowerQuery (q:List Bool):=pair (pairFst (pairFst q)) (pair (pairFst (pairSnd (pairFst q))) (pairSnd q))
theorem lowerQuery_FP:lowerQuery∈FP:=by polytime [lowerQuery]
theorem lowerQuery_packet (c w:List Bool) (o ell j:ℕ):
    lowerQuery (pair (payload c w o ell) (BinaryNatCode.encode j))=payload c w o j:=by
  simp only [lowerQuery,FormulaSignSlotRadialImplicitValueSelection.packet,pairFst_pair,pairSnd_pair]
noncomputable def Lower (z:List Bool):Prop:=∀j<order z,
  FormulaSignSlotRadialImplicitValueTest.Zero (lowerQuery (pair z (BinaryNatCode.encode j)))
noncomputable def Bound (z:List Bool):Prop:=order z≤FormulaSignSlotRadialImplicitValueSelection.coefficientBound z
noncomputable def At (z:List Bool):Prop:=FormulaSignSlotRadialImplicitValueSelection.Guards z ∧
  Bound z ∧Lower z ∧FormulaSignSlotRadialImplicitValueTest.Empty z

theorem lower_evaluator:SpaceFunction (fun z=>[decide (Lower z)]):=by
  have E:=FormulaSignSlotRadialImplicitValueTest.zero_evaluator.precompose lowerQuery lowerQuery_FP
  exact IntegralPolynomialWindowTarskiDecision.flag_all _ _ E (BinaryFn.fromBits (show (fun z=>pairSnd (pairSnd z))∈FP by polytime))
theorem at_evaluator:SpaceFunction (fun z=>[decide (At z)]):=by
  have HB0:=SpaceFunction.ofFP _ (((BinaryFn.fromBits (show (fun z=>pairSnd (pairSnd z))∈FP by polytime)).le
    FormulaSignSlotRadialImplicitValueSelection.coefficientBound_binary).flag_mem_FP)
  have HB:SpaceFunction (fun z=>[decide (Bound z)]):=HB0.congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Bound,FormulaSignSlotRadialImplicitValueSelection.order,decide_eq_true_eq])
  exact IntegralPolynomialWindowTarskiDecision.flag_and _ _ FormulaSignSlotRadialImplicitValueSelection.evaluator
    (IntegralPolynomialWindowTarskiDecision.flag_and _ _ HB
      (IntegralPolynomialWindowTarskiDecision.flag_and _ _ lower_evaluator FormulaSignSlotRadialImplicitValueTest.empty_evaluator))

noncomputable def root (p:List Bool):=original (pairFst p)
noncomputable def count (p:List Bool):=FormulaSignSlotRadialValueCatalogueLayout.outerCount (root p)
noncomputable def row (q:List Bool):=pair (pairFst q) (pair (pairSnd q)
  (pairSnd (FormulaSignSlotRadialValueCatalogueLayout.context (pair (root (pairFst q)) (pairSnd q)))))
theorem root_FP:root∈FP:=mem_FP_comp pairFst_mem_FP FormulaSignSlotRadialImplicitValueSelection.original_FP
theorem count_binary:BinaryFn count:=FormulaSignSlotRadialValueCatalogueLayout.outerCount_binary.comp root_FP
attribute [local irreducible] root FormulaSignSlotRadialValueCatalogueLayout.context
theorem row_FP:row∈FP:=mem_FP_pair pairFst_mem_FP (mem_FP_pair pairSnd_mem_FP
  (mem_FP_comp (mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP root_FP) pairSnd_mem_FP)
    FormulaSignSlotRadialValueCatalogueLayout.context_FP) pairSnd_mem_FP))

theorem row_packet (c w:List Bool) (o:ℕ):row (pair (pair c w) (BinaryNatCode.encode o))=
    payload c w o (FormulaSignSlotRadialValueCatalogueLayout.orderIndex (original c) o):=by
  simp only [row,root,FormulaSignSlotRadialValueCatalogueLayout.context_packet,
    FormulaSignSlotRadialImplicitValueSelection.packet,pairFst_pair,pairSnd_pair]
noncomputable def Holds (p:List Bool):Prop:=∃o,o<count p∧At (row (pair p (BinaryNatCode.encode o)))
theorem evaluator:SpaceFunction (fun p=>[decide (Holds p)]):=
  IntegralPolynomialWindowTarskiDecision.flag_exists _ _ (at_evaluator.precompose row row_FP) count_binary
noncomputable def language:Language:={p|p∈FormulaSignSlotRadialJointStratumSampler.language∧Holds p}
theorem decider:SpaceDecider language:=by
  have E:=IntegralPolynomialWindowTarskiDecision.flag_and _ _
    (ImplicitSourceComponentSampler.decider FormulaSignSlotRadialJointStratum.source
      FormulaSignSlotRadialJointStratumNative.access FormulaSignSlotRadialJointStratumSampler.positive).flagEvaluator evaluator
  apply E.decider (fun z=>decide (z=[true])) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro p
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE:language∈PSPACE:=decider.mem_PSPACE

def NoRoot (p:Polynomial ℝ) (b:ℝ):Prop:=∀r:ℝ,p.eval r=0 → r ∉ Ioo 0 b
noncomputable def certificate (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (o ell:ℕ):=
  FormulaSignSlotRadialValueWindowMeaning.certificate
    (FormulaSignSlotRadialCenterValueLayout.original (family (payload c w o ell))) (fun j=>env c w hw (4*j))
private theorem order_packet (c w:List Bool) (o ell:ℕ):order (payload c w o ell)=ell:=by
  simp only [FormulaSignSlotRadialImplicitValueSelection.order,FormulaSignSlotRadialImplicitValueSelection.packet,
    pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
private theorem rawContext_order (c w:List Bool) (o ell j:ℕ):FormulaSignSlotRadialImplicitValueSelection.rawContext (payload c w o j)=
    pair (family (payload c w o ell)) (BinaryNatCode.encode j):=by
  simp only [FormulaSignSlotRadialImplicitValueSelection.rawContext,FormulaSignSlotRadialImplicitValueSelection.family,
    FormulaSignSlotRadialImplicitValueSelection.outer,FormulaSignSlotRadialImplicitValueSelection.order,
    FormulaSignSlotRadialImplicitValueSelection.context,FormulaSignSlotRadialImplicitValueSelection.sample,
    FormulaSignSlotRadialImplicitValueSelection.packet,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

attribute [local irreducible] FormulaSignSlotRadialValueWindowMeaning.Guard FormulaSignSlotRadialValueWindowMeaning.head
  FormulaSignSlotRadialValueWindowMeaning.rawHead FormulaSignSlotRadialValueWindowMeaning.certificate
  FormulaSignSlotRadialCenterValuePacking.source FormulaSignSlotRadialValueCertificate.polynomial
  FormulaSignSlotRadialValueCatalogueLayout.family

theorem at_meaning (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (o ell:ℕ) (hb:0<env c w hw 3):
    At (payload c w o ell) ↔FormulaSignSlotRadialValueWindowMeaning.Guard (family (payload c w o ell)) (fun j=>env c w hw (4*j)) ∧
      ell≤FormulaSignSlotRadialCenterValuePacking.degree (family (payload c w o ell)) ∧
      (∀j<ell,(certificate c w hw o ell).coeff j=0) ∧NoRoot ((certificate c w hw o ell).coeff ell) (env c w hw 3):=by
  rw [At,FormulaSignSlotRadialImplicitValueSelection.guards_packet c w hw o ell]
  apply and_congr_right
  intro HG
  dsimp only [FormulaSignSlotRadialImplicitValueSelection.env] at HG
  have HH (j:ℕ):FormulaSignSlotRadialValueWindowMeaning.rawHead
      (FormulaSignSlotRadialImplicitValueSelection.rawContext (payload c w o j)) (fun j=>env c w hw (4*j))=
        (certificate c w hw o ell).coeff j:=by
    rw [rawContext_order c w o ell j,FormulaSignSlotRadialValueWindowMeaning.raw_head_packet,
      FormulaSignSlotRadialValueWindowMeaning.head_specialization _ _ _ HG]
    rfl
  simp only [Bound,order_packet,FormulaSignSlotRadialImplicitValueSelection.coefficientBound]
  apply and_congr_right
  intro _
  apply and_congr
  · unfold Lower
    rw [order_packet]
    simp_rw [lowerQuery_packet,FormulaSignSlotRadialImplicitValueTest.zero_packet c w hw,HH]
  · rw [FormulaSignSlotRadialImplicitValueTest.empty_packet c w hw o ell hb,HH]
    rfl

private theorem trailing_index (P:Polynomial (Polynomial ℝ)) (ell:ℕ) (b:ℝ) (hb:0<b)
    (HL:∀j<ell,P.coeff j=0) (HN:NoRoot (P.coeff ell) b):P≠0∧ell=P.natTrailingDegree:=by
  have Hcoeff:P.coeff ell≠0:=by
    intro H0
    have H:=HN (b/2) (by rw [H0,Polynomial.eval_zero])
    exact H ⟨by linarith,by linarith⟩
  have HP:P≠0:=by intro H0;exact Hcoeff (by rw [H0,Polynomial.coeff_zero])
  refine ⟨HP,le_antisymm ?_ (Polynomial.natTrailingDegree_le_of_ne_zero Hcoeff)⟩
  apply Nat.le_of_not_gt
  intro HE
  exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr HP) (HL _ HE)

private theorem trailing_iff (P:Polynomial (Polynomial ℝ)) (L ell:ℕ) (b:ℝ) (HB:0<b) (HD:P.natDegree≤L):
    (ell≤L ∧(∀j<ell,P.coeff j=0) ∧NoRoot (P.coeff ell) b) ↔
      P≠0 ∧ell=P.natTrailingDegree ∧NoRoot P.trailingCoeff b:=by
  constructor
  · rintro ⟨_,HL,HN⟩
    obtain ⟨HP,HE⟩:=trailing_index P ell b HB HL HN
    exact ⟨HP,HE,by simpa only [HE,Polynomial.trailingCoeff] using HN⟩
  · rintro ⟨_,HE,HN⟩
    refine ⟨?_,?_,?_⟩
    · exact HE ▸ (Polynomial.natTrailingDegree_le_natDegree P).trans HD
    · intro j hj
      exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (hj.trans_eq HE)
    · simpa only [HE,Polynomial.trailingCoeff] using HN

attribute [local irreducible] certificate
theorem at_trailing (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (o ell:ℕ) (hb:0<env c w hw 3):
    At (payload c w o ell) ↔FormulaSignSlotRadialValueWindowMeaning.Guard (family (payload c w o ell)) (fun j=>env c w hw (4*j)) ∧
      certificate c w hw o ell≠0 ∧ell=(certificate c w hw o ell).natTrailingDegree ∧
        NoRoot (certificate c w hw o ell).trailingCoeff (env c w hw 3):=by
  rw [at_meaning c w hw o ell hb]
  apply and_congr_right
  intro HG
  have HD0:(certificate c w hw o ell).natDegree≤FormulaSignSlotRadialCenterValuePacking.degree (family (payload c w o ell)):=by
    unfold certificate
    exact FormulaSignSlotRadialValueWindowMeaning.certificate_degree _ _ HG
  exact trailing_iff _ _ ell _ hb HD0
end LeanCanny.Encoding.FormulaSignSlotRadialImplicitValueInterval

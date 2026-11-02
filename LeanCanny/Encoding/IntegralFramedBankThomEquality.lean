/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankQuery
public import LeanCanny.Algebra.IntegerPolynomialIteratedDerivativeSource
public import LeanCanny.Algebra.ThomEncoding
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers

/-! # Native equality between coordinates of different actual banks

One implicit integer polynomial is evaluated at both complete candidates.
Order zero checks the replayed root; all derivative signs identify the same
real value. Each bank supplies original native controls, not a point oracle.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankThomEquality
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankQuery (Bank)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def context (q : List Bool) := pairFst q
def word (right : Bool) (q : List Bool) := if right then pairSnd (pairSnd q) else pairFst (pairSnd q)
def probe (right : Bool) (r : List Bool) :=
  pair (pair (context (pairFst r)) (word right (pairFst r))) (pairSnd r)
theorem probe_FP (right : Bool) : probe right∈FP := by cases right <;> polytime [probe,context,word]

noncomputable def agrees (A B : Bank) (Q : IntegerPolynomialRootQueriesBits.Source) (q : List Bool) : Prop :=
  ∀ k < Q.degree (context q)+1,
    IntegralFramedBankQuery.value A (IntegerPolynomialIteratedDerivativeBits.source Q)
      (probe false (pair q (BinaryNatCode.encode k)))=
    IntegralFramedBankQuery.value B (IntegerPolynomialIteratedDerivativeBits.source Q)
      (probe true (pair q (BinaryNatCode.encode k)))

noncomputable def language (A B : Bank) (Q : IntegerPolynomialRootQueriesBits.Source) : Language :=
  {q | SquareSampleCompleteVertices.Valid (IntegralFramedBankQuery.input A) (context q) (word false q) ∧
    SquareSampleCompleteVertices.Valid (IntegralFramedBankQuery.input B) (context q) (word true q) ∧ agrees A B Q q}

theorem scanEvaluator (A B : Bank) (hA : IntegralFramedBankQuery.Access A) (hB : IntegralFramedBankQuery.Access B)
    (Q : IntegerPolynomialRootQueriesBits.Source) (hQ : IntegerPolynomialRootQueriesBits.Access Q) :
    SpaceFunction (fun q=>[decide (agrees A B Q q)]) := by
  have D:=IntegerPolynomialIteratedDerivativeBits.access hQ
  have L:=(IntegralFramedBankQuery.evaluator A hA _ D).precompose (probe false) (probe_FP false)
  have R:=(IntegralFramedBankQuery.evaluator B hB _ D).precompose (probe true) (probe_FP true)
  have E:=(L.pairOutputs R).postcompose (fun z=>[decide (pairFst z=pairSnd z)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have ND : BinaryFn (fun q=>Q.degree (context q)):=hQ.degree.comp pairFst_mem_FP
  have N:=ND.add (BinaryFn.const 1)
  exact (E.forall_binary N).congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [agrees,Function.comp_apply,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq])

theorem decider (A B : Bank) (hA : IntegralFramedBankQuery.Access A) (hB : IntegralFramedBankQuery.Access B)
    (Q : IntegerPolynomialRootQueriesBits.Source) (hQ : IntegerPolynomialRootQueriesBits.Access Q) :
    SpaceDecider (language A B Q) := by
  have HA : (fun q=>pair (context q) (word false q))∈FP := by polytime [context,word]
  have HB : (fun q=>pair (context q) (word true q))∈FP := by polytime [context,word]
  have L:=((SquareSampleCompleteVertices.decider (IntegralFramedBankQuery.input_access A hA)).precompose _ HA).flagEvaluator
  have R:=((SquareSampleCompleteVertices.decider (IntegralFramedBankQuery.input_access B hB)).precompose _ HB).flagEvaluator
  apply (L.andFlags (R.andFlags (scanEvaluator A B hA hB Q hQ))).decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,Set.mem_preimage,SquareSampleCompleteVertices.language,
    pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq]

theorem packet (A B : Bank) (Q : IntegerPolynomialRootQueriesBits.Source) (c w v : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedBankQuery.input A) c w)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedBankQuery.input B) c v)
    (hn : Q.polynomial c≠0)
    (hr : (Q.polynomial c).eval₂ (Int.castRingHom ℝ) (IntegralFramedBankQuery.point A c w hw)=0) :
    pair c (pair w v)∈language A B Q ↔
      IntegralFramedBankQuery.point A c w hw=IntegralFramedBankQuery.point B c v hv := by
  have HJ (k : ℕ) : IntegralFramedBankQuery.value A (IntegerPolynomialIteratedDerivativeBits.source Q)
      (pair (pair c w) (BinaryNatCode.encode k))=InfinitesimalSign.encode
      (ThomEncoding.sign ((Q.polynomial c).map (Int.castRingHom ℝ)) (IntegralFramedBankQuery.point A c w hw) k) := by
    rw [IntegralFramedBankQuery.packet _ _ c w _ hw,IntegerPolynomialIteratedDerivativeBits.packet]
    simp only [ThomEncoding.sign,Polynomial.iterate_derivative_map,Polynomial.eval_map]
  have HR (k : ℕ) : IntegralFramedBankQuery.value B (IntegerPolynomialIteratedDerivativeBits.source Q)
      (pair (pair c v) (BinaryNatCode.encode k))=InfinitesimalSign.encode
      (ThomEncoding.sign ((Q.polynomial c).map (Int.castRingHom ℝ)) (IntegralFramedBankQuery.point B c v hv) k) := by
    rw [IntegralFramedBankQuery.packet _ _ c v _ hv,IntegerPolynomialIteratedDerivativeBits.packet]
    simp only [ThomEncoding.sign,Polynomial.iterate_derivative_map,Polynomial.eval_map]
  simp only [language,Set.mem_ofPred_eq,context,word,pairFst_pair,pairSnd_pair,
    Bool.false_eq_true,ite_false,ite_true,hw,hv,true_and,agrees,probe]
  simp_rw [HJ,HR,SquareSampleTestSign.encode_eq_iff]
  let p:=(Q.polynomial c).map (Int.castRingHom ℝ)
  let a:=IntegralFramedBankQuery.point A c w hw
  let b:=IntegralFramedBankQuery.point B c v hv
  have HA : p.eval a=0 := by rw [Polynomial.eval_map]; exact hr
  constructor
  · intro hs
    have H0 : SignType.sign (p.eval b)=0 := by
      have H:=hs 0 (by omega)
      change ThomEncoding.sign p a 0=ThomEncoding.sign p b 0 at H
      simpa only [ThomEncoding.sign,Function.iterate_zero_apply,HA,sign_zero] using H.symm
    exact ThomEncoding.root_eq p ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr hn) (Q.degree c)
      (Polynomial.natDegree_map_le.trans (Q.degree_bound c)) a b HA (sign_eq_zero_iff.mp H0)
      (fun k hk=>hs k (by omega))
  · intro he k _
    rw [he]

end LeanCanny.Encoding.IntegralFramedBankThomEquality

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaStrictWitness
public import LeanCanny.ETR.TermArityFP
/-! # Native syntax and exact size bounds for the component-preserving strict witness -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaStrictWitness
open LeanCanny.Encoding LeanCanny.Computation ETR
open scoped Classical

def squaresBits (q : List Bool) : List Bool :=
  Codec.taggedTwo 2
    (Codec.taggedTwo 3 (Term.variableBits q.length) (Term.variableBits q.length))
    (Codec.taggedTwo 3 (Term.variableBits (q.length+1)) (Term.variableBits (q.length+1)))

def termBits (q : List Bool) : List Bool :=
  Codec.taggedTwo 2
    (Codec.taggedTwo 3
      (Codec.taggedTwo 3 (Term.const (-1)).toData.toBits (TermView.normalize (pairFst q)))
      (squaresBits (pairSnd q))) (Term.const (-1)).toData.toBits

theorem squaresBits_FP : squaresBits ∈ FP := by
  have H0 := Term.variableBits_mem_FP (UnaryFn.length id_mem_FP)
  have H1 := Term.variableBits_mem_FP ((UnaryFn.length id_mem_FP).add (UnaryFn.const 1))
  exact Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 H0 H0) (Codec.taggedTwo_mem_FP 3 H1 H1)

theorem termBits_FP : termBits ∈ FP := by
  have HS : (fun q => squaresBits (pairSnd q)) ∈ FP := mem_FP_comp (f := pairSnd) (g := squaresBits) pairSnd_mem_FP squaresBits_FP
  exact Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3
    (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP _) (mem_FP_comp pairFst_mem_FP TermView.normalize_mem_FP))
    HS) (constFn_mem_FP _)

theorem squaresBits_eq (q : List Bool) : squaresBits q = (squares q.length).toData.toBits := by
  simp only [squaresBits,squares,Term.add_toBits,Term.mul_toBits,Term.variableBits_eq]

theorem termBits_eq (q : List Bool) : termBits q =
    (term (pairSnd q).length (TermView.term (pairFst q))).toData.toBits := by
  simp only [termBits,term,Term.add_toBits,Term.mul_toBits,TermView.normalize_eq_term,squaresBits_eq]

theorem term_bits_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) :
    (fun q => (term (n q) (t q)).toData.toBits) ∈ FP := by
  apply mem_FP_of_eq (mem_FP_comp (mem_FP_pair ht hn.mem_FP) termBits_FP)
  intro q
  simp only [Function.comp_apply,termBits_eq,pairSnd_pair,pairFst_pair,List.length_replicate,
    TermView.term_toBits]

theorem term_size (n : ℕ) (t : Term) : (term n t).toData.size = t.toData.size+8*n+116 := by
  simp only [term,squares,Term.dataSize_add,Term.dataSize_mul,Term.dataSize_var,Term.dataSize_const_neg_one]
  omega

theorem term_polynomial_degree (n : ℕ) (t : Term) : (term n t).toPolynomial.totalDegree ≤ t.degreeBound+2 :=
  (term n t).totalDegree_toPolynomial_le.trans_eq (term_degree n t)

end LeanCanny.Connectivity.FormulaStrictWitness

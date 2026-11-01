/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.WeakCircleCanonicalFormula
public import LeanCanny.Encoding.MonotoneGateSource
/-! # Native polynomial-time writer for the canonical weak-circle endpoint conditions -/
@[expose] public section
namespace LeanCanny.Encoding.WeakCircleCanonicalWriter
open LeanCanny.Computation ETR LeanCanny.Geometry.WeakCircleCanonicalFormula
open scoped Classical

def termDifference (a b : List Bool) : List Bool :=
  Codec.taggedTwo 2 a (Codec.taggedTwo 3 (Term.const (-1)).toData.toBits b)
def eqZero (a : List Bool) : List Bool := Codec.taggedOne 1 a
def nonneg (a : List Bool) : List Bool := Codec.taggedOne 3 (Codec.taggedOne 2 a)
def conjunction (a b : List Bool) : List Bool := Codec.taggedTwo 4 a b
def disjunction (a b : List Bool) : List Bool := Codec.taggedTwo 5 a b

def body (packet : List Bool) : List Bool :=
  let t := pairFst packet
  let i := pairFst (pairSnd packet)
  let j := pairSnd (pairSnd packet)
  conjunction (eqZero j) (conjunction (nonneg i)
    (disjunction (conjunction (nonneg t) (eqZero (termDifference (Codec.taggedTwo 3 i i) t)))
      (conjunction (nonneg (Codec.taggedTwo 3 (Term.const (-1)).toData.toBits t)) (eqZero i))))

theorem body_FP : body ∈ FP := by
  have HT := pairFst_mem_FP
  have HI := mem_FP_comp (f := pairSnd) (g := pairFst) pairSnd_mem_FP pairFst_mem_FP
  have HJ := mem_FP_comp (f := pairSnd) (g := pairSnd) pairSnd_mem_FP pairSnd_mem_FP
  have HE : (fun q => eqZero (pairSnd (pairSnd q))) ∈ FP := Codec.taggedOne_mem_FP 1 HJ
  have HN : (fun q => nonneg (pairFst (pairSnd q))) ∈ FP := Codec.taggedOne_mem_FP 3 (Codec.taggedOne_mem_FP 2 HI)
  have HNT : (fun q => nonneg (pairFst q)) ∈ FP := Codec.taggedOne_mem_FP 3 (Codec.taggedOne_mem_FP 2 HT)
  have HD : (fun q => eqZero (termDifference (Codec.taggedTwo 3 (pairFst (pairSnd q)) (pairFst (pairSnd q))) (pairFst q))) ∈ FP :=
    Codec.taggedOne_mem_FP 1 (Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 HI HI)
      (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP _) HT))
  have HM : (fun q => nonneg (Codec.taggedTwo 3 (Term.const (-1)).toData.toBits (pairFst q))) ∈ FP :=
    Codec.taggedOne_mem_FP 3 (Codec.taggedOne_mem_FP 2 (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP _) HT))
  exact Codec.taggedTwo_mem_FP 4 HE (Codec.taggedTwo_mem_FP 4 HN
    (Codec.taggedTwo_mem_FP 5 (Codec.taggedTwo_mem_FP 4 HNT HD)
      (Codec.taggedTwo_mem_FP 4 HM (Codec.taggedOne_mem_FP 1 HI))))

theorem body_eq (t : Term) (i j : ℕ) :
    body (pair t.toData.toBits (pair (Term.var i).toData.toBits (Term.var j).toData.toBits))=
      (formula t i j).toData.toBits := by
  simp only [body,pairFst_pair,pairSnd_pair,termDifference,eqZero,nonneg,conjunction,disjunction,
    formula,nonnegative,difference,Formula.toData,Codec.taggedOne_toBits,Codec.taggedTwo_toBits,Term.toData]

theorem formula_FP {t : List Bool → Term} {i j : List Bool → ℕ}
    (ht : (fun q => (t q).toData.toBits) ∈ FP) (hi : UnaryFn i) (hj : UnaryFn j) :
    (fun q => (formula (t q) (i q) (j q)).toData.toBits) ∈ FP := by
  have HI := mem_FP_of_eq (Term.variableBits_mem_FP hi) (fun q => Term.variableBits_eq (i q))
  have HJ := mem_FP_of_eq (Term.variableBits_mem_FP hj) (fun q => Term.variableBits_eq (j q))
  exact mem_FP_of_eq (mem_FP_comp (mem_FP_pair ht (mem_FP_pair HI HJ)) body_FP) (fun q => body_eq (t q) (i q) (j q))

end LeanCanny.Encoding.WeakCircleCanonicalWriter

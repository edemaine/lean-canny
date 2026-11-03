/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.TermPowerSumFP
public import LeanCanny.ETR.PartialHomogenization
/-! # Small marked-source terms with large scalars as retained variables

Variables n+4,n+5,n+6,n+7 denote radius, regularization, perturbation and
penalty powers. No large power of two is serialized in these terms.
-/
@[expose] public section
namespace LeanCanny.ETR.BoundedMarkedParameterTerm
open LeanCanny.Encoding MvPolynomial
open scoped BigOperators

def sphere (n : ℕ) : Term := .add (TermPowerSum.term (n+2) 2) (.mul (.const (-1)) (.mul (.var (n+4)) (.var (n+4))))
def mark (t : Term) (n : ℕ) : Term := .add (.mul t t) (.mul (sphere n) (sphere n))
def regular (t : Term) (n N : ℕ) : Term :=
  .add (.mul (.var (n+5)) (.add (.add (.mul (.var (n+6)) (mark t n)) (.mul (.const (-1)) (.var (n+7))))
    (TermPowerSum.term (n+4) N))) (.const (-1))

theorem sum_eval (a K : ℕ) (hK : 0<K) (x : ℕ→ℝ) :
    (TermPowerSum.term a K).eval x=∑ i : Fin a,x i.val^K := by
  have H:=PartialHomogenization.finite_eval (TermPowerSum.term a K) a x (by rw [TermPowerSum.arity a K hK])
  rw [TermPowerSum.finitePolynomial a K a le_rfl] at H
  simpa only [eval₂_sum,eval₂_pow,eval₂_X,Fin.val_castLE] using H.symm

theorem eval_mark (t : Term) (n : ℕ) (x : ℕ→ℝ) :
    (mark t n).eval x=(t.eval x)^2+((∑ i : Fin (n+2),x i.val^2)-(x (n+4))^2)^2 := by
  simp only [mark,sphere,Term.eval,sum_eval _ 2 (by decide),Int.cast_neg,Int.cast_one]
  ring

theorem eval_regular (t : Term) (n N : ℕ) (hN : 0<N) (x : ℕ→ℝ) :
    (regular t n N).eval x=x (n+5)*(x (n+6)*(mark t n).eval x-x (n+7)+∑ i : Fin (n+4),x i.val^N)-1 := by
  simp only [regular,Term.eval,sum_eval _ N hN,Int.cast_neg,Int.cast_one]
  ring

theorem mark_arity (t : Term) (n : ℕ) (ht : t.arity≤n) : (mark t n).arity≤n+8 := by
  simp only [mark,sphere,Term.arity,TermPowerSum.arity _ 2 (by decide)]
  omega

theorem regular_arity (t : Term) (n N : ℕ) (ht : t.arity≤n) (hN : 0<N) : (regular t n N).arity≤n+8 := by
  have H:=mark_arity t n ht
  simp only [regular,Term.arity,TermPowerSum.arity _ N hN]
  omega

private theorem add_FP {t u : List Bool→Term} (ht : (fun c=>(t c).toData.toBits)∈FP)
    (hu : (fun c=>(u c).toData.toBits)∈FP) : (fun c=>(Term.add (t c) (u c)).toData.toBits)∈FP := by
  simpa only [Term.add_toBits] using Codec.taggedTwo_mem_FP 2 ht hu
private theorem mul_FP {t u : List Bool→Term} (ht : (fun c=>(t c).toData.toBits)∈FP)
    (hu : (fun c=>(u c).toData.toBits)∈FP) : (fun c=>(Term.mul (t c) (u c)).toData.toBits)∈FP := by
  simpa only [Term.mul_toBits] using Codec.taggedTwo_mem_FP 3 ht hu
private theorem var_FP {i : List Bool→ℕ} (hi : UnaryFn i) : (fun c=>(Term.var (i c)).toData.toBits)∈FP:=
  mem_FP_of_eq (Term.variableBits_mem_FP hi) (fun _=>Term.variableBits_eq _)

theorem sphere_FP {n : List Bool→ℕ} (hn : UnaryFn n) : (fun c=>(sphere (n c)).toData.toBits)∈FP :=
  add_FP (TermPowerSum.encode_mem_FP (hn.add (UnaryFn.const 2)) (UnaryFn.const 2))
    (mul_FP (constFn_mem_FP _) (mul_FP (var_FP (hn.add (UnaryFn.const 4))) (var_FP (hn.add (UnaryFn.const 4)))))

theorem mark_FP {t : List Bool→Term} {n : List Bool→ℕ} (ht : (fun c=>(t c).toData.toBits)∈FP) (hn : UnaryFn n) :
    (fun c=>(mark (t c) (n c)).toData.toBits)∈FP :=
  add_FP (mul_FP ht ht) (mul_FP (sphere_FP hn) (sphere_FP hn))

theorem regular_FP {t : List Bool→Term} {n N : List Bool→ℕ} (ht : (fun c=>(t c).toData.toBits)∈FP)
    (hn : UnaryFn n) (hN : UnaryFn N) : (fun c=>(regular (t c) (n c) (N c)).toData.toBits)∈FP :=
  add_FP (mul_FP (var_FP (hn.add (UnaryFn.const 5)))
    (add_FP (add_FP (mul_FP (var_FP (hn.add (UnaryFn.const 6))) (mark_FP ht hn))
      (mul_FP (constFn_mem_FP _) (var_FP (hn.add (UnaryFn.const 7)))))
      (TermPowerSum.encode_mem_FP (hn.add (UnaryFn.const 4)) hN))) (constFn_mem_FP _)

end LeanCanny.ETR.BoundedMarkedParameterTerm

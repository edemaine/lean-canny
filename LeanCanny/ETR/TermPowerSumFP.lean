/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TermSumFP
public import LeanCanny.ETR.TermPowerFP

/-! # Native writing of finite sums of coordinate powers -/

@[expose] public section
namespace LeanCanny.ETR.TermSum
open MvPolynomial
open scoped BigOperators

theorem finitePolynomial_accumulate (ts : List Term) (acc : Term) (A : ℕ) :
    (accumulate ts acc).finitePolynomial A = acc.finitePolynomial A + (ts.map (Term.finitePolynomial A)).sum := by
  induction ts generalizing acc with
  | nil => simp [accumulate]
  | cons t ts ih =>
    change (accumulate ts (.add t acc)).finitePolynomial A = _
    rw [ih]
    simp only [Term.finitePolynomial, List.map_cons, List.sum_cons]
    ring

end LeanCanny.ETR.TermSum

namespace LeanCanny.ETR.TermPowerSum
open LeanCanny.Encoding LeanCanny.Encoding.Brackets MvPolynomial
open scoped BigOperators

def terms (n k : ℕ) : List Term := (List.range n).map (fun i => (Term.var i).power k)
def term (n k : ℕ) : Term := TermSum.accumulate (terms n k) (.const 0)

theorem term_succ (n k : ℕ) : term (n + 1) k = .add ((Term.var n).power k) (term n k) := by
  simp only [term, terms, List.range_succ, List.map_append, List.map_singleton,
    TermSum.accumulate, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem arity (n k : ℕ) (hk : 0 < k) : (term n k).arity = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [term_succ, Term.arity, Term.arity_power _ _ hk, Term.arity, ih]
    omega

private theorem sum_range {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem finitePolynomial (n k A : ℕ) (hn : n ≤ A) :
    (term n k).finitePolynomial A = ∑ i : Fin n, (X (i.castLE hn) : MvPolynomial (Fin A) ℤ) ^ k := by
  rw [term, TermSum.finitePolynomial_accumulate]
  simp only [Term.finitePolynomial, C_0, zero_add, terms, List.map_map, Function.comp_def]
  rw [sum_range, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [Term.finitePolynomial_power]
  simp only [Term.finitePolynomial, dite_eq_left (i.isLt.trans_le hn)]
  rfl

theorem encode_mem_FP {n k : List Bool → ℕ} (hn : UnaryFn n) (hk : UnaryFn k) :
    (fun c => (term (n c) (k c)).toData.toBits) ∈ FP := by
  have hpower := TermPower.write_mem_FP
    (Term.variableBits_mem_FP (UnaryFn.length pairSnd_mem_FP)) (hk.comp pairFst_mem_FP)
  have hl := flatMap_range_mem_FP hpower hn.mem_FP
  have he := mem_FP_comp (mem_FP_comp hl wrap_mem_FP) TermSum.collapse_mem_FP
  apply mem_FP_of_eq he
  intro c
  simp only [Function.comp_apply, TermPower.write_correct, pairFst_pair, pairSnd_pair,
    Term.variableBits_eq, TermView.term_toBits, List.length_replicate]
  have hh : (List.range (n c)).flatMap (fun i => ((Term.var i).power (k c)).toData.toBits) =
      SumSquares.forest (terms (n c) (k c)) := by
    simp only [terms, SumSquares.forest, List.map_map, List.flatten_eq_flatMap,
      List.flatMap_map, Function.comp_def, id_eq]
  rw [hh]
  have hb : wrap (SumSquares.forest (terms (n c) (k c))) = SumSquares.listBits (terms (n c) (k c)) := by
    simp only [SumSquares.listBits, SumSquares.forest, Data.toBits_l, List.map_map, Function.comp_def]
    rfl
  rw [hb, TermSum.collapse_listBits]
  rfl

end LeanCanny.ETR.TermPowerSum

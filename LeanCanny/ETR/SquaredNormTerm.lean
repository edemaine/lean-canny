/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.BoundedMonotoneGateBounds
/-! # A native quadratic feature independent of every later radial center -/
@[expose] public section
namespace LeanCanny.ETR.SquaredNormTerm
open LeanCanny.Encoding LeanCanny.Computation
open scoped BigOperators

def entries (n : ℕ) : List Term := (List.range n).map Term.var

def term (n : ℕ) : Term := SumSquares.accumulate (entries n) (.const 0)

theorem term_FP {N : List Bool → ℕ} (hN : UnaryFn N) :
    (fun c => (term (N c)).toData.toBits)∈FP := by
  have HV : (fun q : List Bool => (Term.var (pairSnd q).length).toData.toBits)∈FP :=
    mem_FP_of_eq (Term.variableBits_mem_FP (UnaryFn.length pairSnd_mem_FP)) (fun _ => Term.variableBits_eq _)
  have H := flatMap_range_mem_FP HV hN.mem_FP
  have HB : (fun c => SumSquares.listBits (entries (N c)))∈FP := by
    apply mem_FP_of_eq (mem_FP_comp H Brackets.wrap_mem_FP)
    intro c
    simp only [Function.comp_apply,entries,SumSquares.listBits,Data.toBits_l,List.map_map,
      List.flatten_eq_flatMap,List.flatMap_map,Function.comp_def,id_eq,Brackets.wrap,pairSnd_pair,List.length_replicate]
  apply mem_FP_of_eq (mem_FP_comp HB SumSquares.collapse_mem_FP)
  intro c
  rw [Function.comp_apply,SumSquares.collapse_listBits]
  rfl

theorem scope (n : ℕ) : (term n).arity≤n := by
  apply SumSquares.arity_accumulate_le _ _ _ (Nat.zero_le _)
  simp only [entries,List.forall_mem_map,List.mem_range,Term.arity]
  exact fun i hi => hi

private theorem eval_squares (ts : List Term) (env : ℕ → ℝ) :
    (Term.sumSquares ts).eval env=(ts.map (fun t => (t.eval env)^2)).sum := by
  induction ts with
  | nil => simp [Term.sumSquares,Term.eval]
  | cons t ts IH => simp only [Term.sumSquares,Term.eval,Term.square,List.map_cons,List.sum_cons,IH,pow_two]

theorem eval (n : ℕ) (env : ℕ → ℝ) : (term n).eval env=∑ i : Fin n, (env i)^2 := by
  rw [term,SumSquares.eval_accumulate,eval_squares]
  simp only [Term.eval,Int.cast_zero,zero_add,entries,List.map_map,Function.comp_def]
  rw [← List.sum_toFinset _ (List.nodup_range (n:=n)),List.toFinset_range]
  exact (Fin.sum_univ_eq_sum_range (fun i => env i^2) n).symm

private theorem accumulate_degree (ts : List Term) (acc : Term)
    (HA : acc.degreeBound≤2) (HT : ∀ t∈ts,t.degreeBound≤1) :
    (SumSquares.accumulate ts acc).degreeBound≤2 := by
  induction ts generalizing acc with
  | nil => exact HA
  | cons t ts IH =>
    apply IH
    · have H := HT t List.mem_cons_self
      simp only [Term.square,Term.degreeBound]
      omega
    · exact fun t ht => HT t (List.mem_cons_of_mem _ ht)

theorem degree (n : ℕ) : (term n).degreeBound≤2 := by
  apply accumulate_degree _ _ (Nat.zero_le _)
  simp only [entries,List.forall_mem_map,Term.degreeBound,le_refl,implies_true]

end LeanCanny.ETR.SquaredNormTerm

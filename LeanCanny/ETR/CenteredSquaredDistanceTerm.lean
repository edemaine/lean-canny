/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.SquaredNormTerm
/-! # A native universal radial feature with centers stored as spatial coordinates -/
@[expose] public section
namespace LeanCanny.ETR.CenteredSquaredDistanceTerm
open LeanCanny.Encoding LeanCanny.Computation
open scoped BigOperators

def difference (offset i : ℕ) : Term := .add (.var i) (.mul (.const (-1)) (.var (offset+i)))
def entries (offset n : ℕ) := (List.range n).map (difference offset)
def term (offset n : ℕ) := SumSquares.accumulate (entries offset n) (.const 0)

theorem term_FP {N d : List Bool → ℕ} (hN : UnaryFn N) (hd : UnaryFn d) :
    (fun c => (term (N c) (d c)).toData.toBits)∈FP := by
  have HI := UnaryFn.length pairSnd_mem_FP
  have HO := (hN.comp pairFst_mem_FP).add HI
  have HV : (fun q : List Bool => (Term.var (pairSnd q).length).toData.toBits)∈FP :=
    mem_FP_of_eq (Term.variableBits_mem_FP HI) (fun _ => Term.variableBits_eq _)
  have HW : (fun q : List Bool => (Term.var (N (pairFst q)+(pairSnd q).length)).toData.toBits)∈FP :=
    mem_FP_of_eq (Term.variableBits_mem_FP HO) (fun _ => Term.variableBits_eq _)
  have HN : (fun q => (Term.mul (.const (-1)) (.var (N (pairFst q)+(pairSnd q).length))).toData.toBits)∈FP :=
    mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) HW)
      (fun _ => (Term.mul_toBits _ _).symm)
  have HD : (fun q => (difference (N (pairFst q)) (pairSnd q).length).toData.toBits)∈FP :=
    mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 HV HN) (fun _ => (Term.add_toBits _ _).symm)
  have H := flatMap_range_mem_FP HD hd.mem_FP
  have HB : (fun c => SumSquares.listBits (entries (N c) (d c)))∈FP := by
    apply mem_FP_of_eq (mem_FP_comp H Brackets.wrap_mem_FP)
    intro c
    simp only [Function.comp_apply,entries,SumSquares.listBits,Data.toBits_l,List.map_map,
      List.flatten_eq_flatMap,List.flatMap_map,Function.comp_def,id_eq,Brackets.wrap,pairFst_pair,pairSnd_pair,
      List.length_replicate]
  apply mem_FP_of_eq (mem_FP_comp HB SumSquares.collapse_mem_FP)
  intro c
  rw [Function.comp_apply,SumSquares.collapse_listBits]
  rfl

theorem scope (offset n : ℕ) : (term offset n).arity≤offset+n := by
  apply SumSquares.arity_accumulate_le _ _ _ (Nat.zero_le _)
  simp only [entries,List.forall_mem_map,List.mem_range,difference,Term.arity]
  intro i hi
  omega

private theorem eval_squares (ts : List Term) (env : ℕ → ℝ) :
    (Term.sumSquares ts).eval env=(ts.map (fun t => (t.eval env)^2)).sum := by
  induction ts with
  | nil => simp [Term.sumSquares,Term.eval]
  | cons t ts IH => simp only [Term.sumSquares,Term.eval,Term.square,List.map_cons,List.sum_cons,IH,pow_two]

theorem eval (offset n : ℕ) (env : ℕ → ℝ) :
    (term offset n).eval env=∑ i : Fin n, (env i-env (offset+i))^2 := by
  rw [term,SumSquares.eval_accumulate,eval_squares]
  simp only [Term.eval,Int.cast_zero,zero_add,entries,List.map_map,Function.comp_def,difference,
    Int.cast_neg,Int.cast_one,neg_one_mul,← sub_eq_add_neg]
  rw [← List.sum_toFinset _ (List.nodup_range (n:=n)),List.toFinset_range]
  exact (Fin.sum_univ_eq_sum_range (fun i => (env i-env (offset+i))^2) n).symm

end LeanCanny.ETR.CenteredSquaredDistanceTerm

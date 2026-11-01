/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.NNFEncoding
public import LeanCanny.ETR.FormulaView
public import LeanCanny.ETR.EquationSize
public import LeanCanny.ETR.SumSquaresFP
public import LeanCanny.Encoding.BracketAccess
/-! # A native traversal extracts strict-OR atoms without entering their arithmetic payloads -/
@[expose] public section
namespace LeanCanny.ETR.StrictOrTraversal
open LeanCanny.Encoding LeanCanny.Encoding.Brackets
open scoped Classical

def negative (term : List Bool) : List Bool := Codec.taggedTwo 3 (Term.const (-1)).toData.toBits term

def step (state : List Bool) : List Bool :=
  let todo := pairFst state
  let out := pairSnd state
  let node := firstNode todo
  let tail := afterNode todo
  if todo=[] then state else
  if NNF.HasTwo 5 node then pair (NNF.second node++NNF.third node++tail) out else
  pair tail (if NNF.HasOne 2 node then out++negative (NNF.second node) else out)

attribute [local irreducible] pair pairFst pairSnd firstNode afterNode NNF.second NNF.third

theorem negative_FP : negative ∈ FP := Codec.taggedTwo_mem_FP 3 (constFn_mem_FP _) id_mem_FP

theorem step_FP : step ∈ FP := by
  have HN := mem_FP_comp pairFst_mem_FP firstNode_mem_FP
  have HT := mem_FP_comp pairFst_mem_FP afterNode_mem_FP
  have H2 := mem_FP_comp HN NNF.second_mem_FP
  have H3 := mem_FP_comp HN NNF.third_mem_FP
  have HE : FPPred (fun state : List Bool => pairFst state=[]) :=
    (FPPred.eq (UnaryFn.length pairFst_mem_FP) (UnaryFn.const 0)).of_iff (fun q => by simp)
  exact HE.ite_mem_FP id_mem_FP (((NNF.hasTwo_fppred 5).comp HN).ite_mem_FP
    (mem_FP_pair (appendFn_mem_FP (appendFn_mem_FP H2 H3) HT) pairSnd_mem_FP)
    (mem_FP_pair HT (((NNF.hasOne_fppred 2).comp HN).ite_mem_FP
      (appendFn_mem_FP pairSnd_mem_FP (mem_FP_comp H2 negative_FP)) pairSnd_mem_FP)))

theorem split_length (todo : List Bool) : (firstNode todo).length+(afterNode todo).length=todo.length := by
  have H:=congrArg List.length (List.take_append_drop (nodeLength todo) todo)
  simpa only [firstNode,afterNode,List.length_append] using H

theorem taggedOne_length (k : ℕ) (a : List Bool) : (Codec.taggedOne k a).length=2*k+a.length+4 := by
  simp only [Codec.taggedOne,wrap,List.length_cons,List.length_append,Data.length_toBits,
    Codec.unary_size,List.length_nil]
  omega

theorem step_pair_length (todo out : List Bool) :
    (step (pair todo out)).length≤(pair todo out).length+22 := by
  have HS:=split_length todo
  by_cases HE : todo=[]
  · simp only [step,pairFst_pair,pairSnd_pair,ite_eq_left HE]
    omega
  · by_cases HO : NNF.HasTwo 5 (firstNode todo)
    · have HL := congrArg List.length HO.1
      rw [SumSquares.taggedTwo_length] at HL
      simp only [step,pairFst_pair,pairSnd_pair,ite_eq_right HE,ite_eq_left HO,pair_length,List.length_append]
      omega
    · by_cases HA : NNF.HasOne 2 (firstNode todo)
      · have HL := congrArg List.length HA.1
        rw [taggedOne_length] at HL
        have HN : (negative (NNF.second (firstNode todo))).length=22+(NNF.second (firstNode todo)).length := by
          simp only [negative,SumSquares.taggedTwo_length,Data.length_toBits,Term.dataSize_const_neg_one]
          omega
        simp only [step,pairFst_pair,pairSnd_pair,ite_eq_right HE,ite_eq_right HO,ite_eq_left HA,
          pair_length,List.length_append,HN]
        omega
      · simp only [step,pairFst_pair,pairSnd_pair,ite_eq_right HE,ite_eq_right HO,ite_eq_right HA,pair_length]
        omega

theorem step_pair_exists (todo out : List Bool) : ∃ todo' out', step (pair todo out)=pair todo' out' := by
  by_cases HE : todo=[]
  · exact ⟨todo,out,by simp only [step,pairFst_pair,pairSnd_pair,ite_eq_left HE]⟩
  · by_cases HO : NNF.HasTwo 5 (firstNode todo)
    · exact ⟨NNF.second (firstNode todo)++NNF.third (firstNode todo)++afterNode todo,out,
        by simp only [step,pairFst_pair,pairSnd_pair,ite_eq_right HE,ite_eq_left HO]⟩
    · exact ⟨afterNode todo,if NNF.HasOne 2 (firstNode todo) then out++negative (NNF.second (firstNode todo)) else out,
        by simp only [step,pairFst_pair,pairSnd_pair,ite_eq_right HE,ite_eq_right HO]⟩

theorem iterate_pair_exists (n : ℕ) (todo out : List Bool) :
    ∃ todo' out', step^[n] (pair todo out)=pair todo' out' := by
  induction n with
  | zero => exact ⟨todo,out,rfl⟩
  | succ n IH =>
    obtain ⟨todo',out',H⟩ := IH
    rw [Function.iterate_succ_apply',H]
    exact step_pair_exists todo' out'

def init (bits : List Bool) : List Bool := pair (FormulaView.normalize bits) []
def forest (bits : List Bool) : List Bool := pairSnd (step^[(FormulaView.normalize bits).length] (init bits))

theorem forest_FP : forest ∈ FP := by
  have HI : init ∈ FP := mem_FP_pair FormulaView.normalize_mem_FP (constFn_mem_FP [])
  have HL := iterate_mem_FP_of_step_le step_FP HI FormulaView.normalize_mem_FP 22
    (fun z n _ => by
      obtain ⟨todo,out,H⟩ := iterate_pair_exists n (FormulaView.normalize z) []
      change (step^[n+1] (pair (FormulaView.normalize z) [])).length≤(step^[n] (pair (FormulaView.normalize z) [])).length+22
      rw [Function.iterate_succ_apply',H]
      exact step_pair_length todo out)
  exact mem_FP_comp HL pairSnd_mem_FP

end LeanCanny.ETR.StrictOrTraversal

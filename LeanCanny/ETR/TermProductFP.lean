/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.SumSquaresFP
public import LeanCanny.ETR.EquationDegree

/-! # Native multiplication of a serialized term list

Each consumed term is added to the accumulator. The raw state grows by at
most eight bits per step, including on malformed inputs; coefficient payloads
are copied without conversion to unary.
-/

@[expose] public section
namespace LeanCanny.ETR.TermProduct
open LeanCanny.Encoding.Brackets

def step (state : List Bool) : List Bool :=
  let todo := pairFst state
  if todo = [] then state else pair (afterNode todo)
    (Codec.taggedTwo 3 (firstNode todo) (pairSnd state))

theorem step_mem_FP : step ∈ FP := by
  have ht := mem_FP_comp pairFst_mem_FP firstNode_mem_FP
  have hr := mem_FP_comp pairFst_mem_FP afterNode_mem_FP
  have he : FPPred (fun state => pairFst state = []) :=
    (FPPred.eq (UnaryFn.length pairFst_mem_FP) (UnaryFn.const 0)).of_iff (by intro state; simp)
  exact he.ite_mem_FP id_mem_FP (mem_FP_pair hr (Codec.taggedTwo_mem_FP 3 ht pairSnd_mem_FP))

theorem step_pair_exists (todo acc : List Bool) :
    ∃ todo' acc', step (pair todo acc) = pair todo' acc' := by
  by_cases he : todo = []
  · exact ⟨todo, acc, by simp [step, he]⟩
  · exact ⟨afterNode todo, Codec.taggedTwo 3 (firstNode todo) acc, by simp [step, he]⟩

theorem iterate_pair_exists (n : ℕ) (todo acc : List Bool) :
    ∃ todo' acc', step^[n] (pair todo acc) = pair todo' acc' := by
  induction n with
  | zero => exact ⟨todo, acc, rfl⟩
  | succ n ih =>
    obtain ⟨todo', acc', hi⟩ := ih
    rw [Function.iterate_succ_apply', hi]
    exact step_pair_exists todo' acc'

theorem step_pair_length_le (todo acc : List Bool) :
    (step (pair todo acc)).length ≤ (pair todo acc).length + 10 := by
  have hp : (firstNode todo).length + (afterNode todo).length = todo.length := by
    have hh := congrArg List.length (List.take_append_drop (nodeLength todo) todo)
    simpa only [List.length_append, firstNode, afterNode] using hh
  by_cases he : todo = []
  · simp [step, he]
  · simp only [step, pairFst_pair, pairSnd_pair, ite_eq_right he, pair_length, SumSquares.taggedTwo_length]
    omega

def init (bits : List Bool) : List Bool := pair (contents bits) (Term.const 1).toData.toBits
def collapse (bits : List Bool) : List Bool := pairSnd (step^[(contents bits).length] (init bits))

theorem collapse_mem_FP : collapse ∈ FP := by
  have hi : init ∈ FP := mem_FP_pair contents_mem_FP (constFn_mem_FP _)
  have hloop := iterate_mem_FP_of_step_le step_mem_FP hi contents_mem_FP 10 (fun z n _ => by
    obtain ⟨todo, acc, he⟩ := iterate_pair_exists n (contents z) (Term.const 1).toData.toBits
    change (step^[n + 1] (pair (contents z) (Term.const 1).toData.toBits)).length ≤
      (step^[n] (pair (contents z) (Term.const 1).toData.toBits)).length + 10
    rw [Function.iterate_succ_apply', he]
    exact step_pair_length_le todo acc)
  exact mem_FP_comp hloop pairSnd_mem_FP

def accumulate (ts : List Term) (acc : Term) : Term := ts.foldl (fun a t => .mul t a) acc

theorem step_term_cons (t : Term) (ts : List Term) (acc : Term) :
    step (pair (SumSquares.forest (t :: ts)) acc.toData.toBits) =
      pair (SumSquares.forest ts) (Term.mul t acc).toData.toBits := by
  have hn : SumSquares.forest (t :: ts) ≠ [] := by
    have hl := SumSquares.forest_length_ge (t :: ts)
    intro he
    rw [he] at hl
    simp at hl
  rw [step, pairFst_pair, pairSnd_pair, ite_eq_right hn, SumSquares.forest_cons,
    afterNode_toBits_append, firstNode_toBits_append]
  rw [Term.mul_toBits]

theorem iterate_terms (ts : List Term) (acc : Term) (n : ℕ) (hn : ts.length ≤ n) :
    step^[n] (pair (SumSquares.forest ts) acc.toData.toBits) = pair [] (accumulate ts acc).toData.toBits := by
  induction ts generalizing acc n with
  | nil =>
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by simp)]
      simp [step, accumulate]
  | cons t ts ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      rw [Function.iterate_succ_apply, step_term_cons]
      exact ih _ n (by simp only [List.length_cons] at hn; omega)

theorem collapse_listBits (ts : List Term) :
    collapse (SumSquares.listBits ts) = (accumulate ts (.const 1)).toData.toBits := by
  rw [collapse, init, SumSquares.contents_listBits,
    iterate_terms ts (.const 1) _ (SumSquares.forest_length_ge ts), pairSnd_pair]

theorem eval_accumulate (ts : List Term) (acc : Term) (x : ℕ → ℝ) :
    (accumulate ts acc).eval x = acc.eval x * (ts.map (fun t => t.eval x)).prod := by
  induction ts generalizing acc with
  | nil => simp [accumulate]
  | cons t ts ih =>
    change (accumulate ts (.mul t acc)).eval x = _
    rw [ih]
    simp only [Term.eval, List.map_cons, List.prod_cons]
    ring

theorem degree_accumulate (ts : List Term) (acc : Term) :
    (accumulate ts acc).degreeBound=acc.degreeBound+(ts.map Term.degreeBound).sum := by
  induction ts generalizing acc with
  | nil => simp [accumulate]
  | cons t ts IH =>
    change (accumulate ts (.mul t acc)).degreeBound=_
    rw [IH]
    simp only [Term.degreeBound,List.map_cons,List.sum_cons]
    omega

theorem arity_accumulate_le (ts : List Term) (acc : Term) (A : ℕ)
    (hacc : acc.arity≤A) (ht : ∀ t∈ts,t.arity≤A) : (accumulate ts acc).arity≤A := by
  induction ts generalizing acc with
  | nil => exact hacc
  | cons t ts IH =>
    apply IH
    · exact max_le (ht t List.mem_cons_self) hacc
    · exact fun t h => ht t (List.mem_cons_of_mem _ h)

end LeanCanny.ETR.TermProduct

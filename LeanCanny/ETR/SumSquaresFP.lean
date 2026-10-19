/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationSize
public import LeanCanny.ETR.EncodingFP

/-!
# A polynomial-time sum-of-squares writer

The input is an encoded list of polynomial terms. The loop splits off one
serialized term per round and adds its square to the accumulated expression.
Its paired state has a potential that grows by at most eighteen bits per round,
including on malformed input strings. The semantic theorem is stated on encoded
term lists, as supplied by the normalization compiler.
-/

@[expose] public section

namespace LeanCanny.ETR.SumSquares
open Complexity
open LeanCanny.Encoding.Brackets

def addSquareBits (term acc : List Bool) : List Bool :=
  Codec.taggedTwo 2 (Codec.taggedTwo 3 term term) acc

theorem taggedTwo_length (tag : ℕ) (a b : List Bool) :
    (Codec.taggedTwo tag a b).length = 2 * tag + a.length + b.length + 4 := by
  simp only [Codec.taggedTwo, wrap, List.length_cons, List.length_append,
    Data.length_toBits, Codec.unary_size, List.length_nil]
  omega

theorem addSquareBits_length (term acc : List Bool) :
    (addSquareBits term acc).length = 2 * term.length + acc.length + 18 := by
  simp only [addSquareBits, taggedTwo_length]
  omega

theorem addSquareBits_mem_FP {term acc : List Bool → List Bool} (ht : term ∈ FP) (ha : acc ∈ FP) :
    (fun z => addSquareBits (term z) (acc z)) ∈ FP :=
  Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 ht ht) ha

theorem addSquareBits_toBits (t acc : Term) :
    addSquareBits t.toData.toBits acc.toData.toBits = (Term.add t.square acc).toData.toBits := by
  simp only [addSquareBits, Term.add_toBits, Term.square, Term.mul_toBits]

def step (state : List Bool) : List Bool :=
  let todo := pairFst state
  if todo = [] then state
  else pair (afterNode todo) (addSquareBits (firstNode todo) (pairSnd state))

theorem step_mem_FP : step ∈ FP := by
  have ht := mem_FP_comp pairFst_mem_FP firstNode_mem_FP
  have hr := mem_FP_comp pairFst_mem_FP afterNode_mem_FP
  have he : FPPred fun state => pairFst state = [] :=
    (FPPred.eq (UnaryFn.length pairFst_mem_FP) (UnaryFn.const 0)).of_iff (by intro state; simp)
  exact he.ite_mem_FP id_mem_FP (mem_FP_pair hr (addSquareBits_mem_FP ht pairSnd_mem_FP))

theorem step_pair_exists (todo acc : List Bool) :
    ∃ todo' acc', step (pair todo acc) = pair todo' acc' := by
  by_cases he : todo = []
  · exact ⟨todo, acc, by simp [step, he]⟩
  · exact ⟨afterNode todo, addSquareBits (firstNode todo) acc, by simp [step, he]⟩

theorem iterate_pair_exists (n : ℕ) (todo acc : List Bool) :
    ∃ todo' acc', step^[n] (pair todo acc) = pair todo' acc' := by
  induction n with
  | zero => exact ⟨todo, acc, rfl⟩
  | succ n ih =>
      obtain ⟨todo', acc', hi⟩ := ih
      rw [Function.iterate_succ_apply', hi]
      exact step_pair_exists todo' acc'

theorem step_pair_length_le (todo acc : List Bool) :
    (step (pair todo acc)).length ≤ (pair todo acc).length + 18 := by
  have hp : (firstNode todo).length + (afterNode todo).length = todo.length := by
    have hh := congrArg List.length (List.take_append_drop (nodeLength todo) todo)
    simpa only [List.length_append, firstNode, afterNode] using hh
  by_cases he : todo = []
  · simp [step, he]
  · simp only [step, pairFst_pair, pairSnd_pair, ite_eq_right he, pair_length, addSquareBits_length]
    omega

def zeroBits : List Bool := (Term.const 0).toData.toBits

def init (bits : List Bool) : List Bool := pair (contents bits) zeroBits

def collapse (bits : List Bool) : List Bool :=
  pairSnd (step^[(contents bits).length] (init bits))

theorem collapse_mem_FP : collapse ∈ FP := by
  have hi : init ∈ FP := mem_FP_pair contents_mem_FP (constFn_mem_FP zeroBits)
  have hloop := iterate_mem_FP_of_step_le step_mem_FP hi contents_mem_FP 18
    (fun z n _ => by
      obtain ⟨todo, acc, he⟩ := iterate_pair_exists n (contents z) zeroBits
      change (step^[n + 1] (pair (contents z) zeroBits)).length ≤
        (step^[n] (pair (contents z) zeroBits)).length + 18
      rw [Function.iterate_succ_apply', he]
      exact step_pair_length_le todo acc)
  exact mem_FP_comp hloop pairSnd_mem_FP

def forest (ts : List Term) : List Bool := (ts.map (fun t => t.toData.toBits)).flatten

@[simp] theorem forest_nil : forest [] = [] := rfl

@[simp] theorem forest_cons (t : Term) (ts : List Term) :
    forest (t :: ts) = t.toData.toBits ++ forest ts := rfl

def accumulate (ts : List Term) (acc : Term) : Term :=
  ts.foldl (fun a t => .add t.square a) acc

theorem forest_length_ge (ts : List Term) : ts.length ≤ (forest ts).length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      have hp : 0 < t.toData.toBits.length := by simp
      simp only [forest_cons, List.length_append, List.length_cons]
      omega

theorem step_term_cons (t : Term) (ts : List Term) (acc : Term) :
    step (pair (forest (t :: ts)) acc.toData.toBits) =
      pair (forest ts) (Term.add t.square acc).toData.toBits := by
  have hn : forest (t :: ts) ≠ [] := by
    have hl := forest_length_ge (t :: ts)
    intro he
    rw [he] at hl
    simp at hl
  rw [step, pairFst_pair, pairSnd_pair, ite_eq_right hn, forest_cons,
    afterNode_toBits_append, firstNode_toBits_append, addSquareBits_toBits]

theorem iterate_terms (ts : List Term) (acc : Term) (n : ℕ) (hn : ts.length ≤ n) :
    step^[n] (pair (forest ts) acc.toData.toBits) = pair [] (accumulate ts acc).toData.toBits := by
  induction ts generalizing acc n with
  | nil =>
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Function.iterate_succ_apply']
          rw [ih (by simp)]
          simp [step, accumulate]
  | cons t ts ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          rw [Function.iterate_succ_apply, step_term_cons]
          exact ih _ n (by simp only [List.length_cons] at hn; omega)

def listBits (ts : List Term) : List Bool := (Data.l (ts.map Term.toData)).toBits

theorem contents_listBits (ts : List Term) : contents (listBits ts) = forest ts := by
  simp only [listBits, contents_toBits, forest, List.map_map, Function.comp_def]

theorem collapse_listBits (ts : List Term) :
    collapse (listBits ts) = (accumulate ts (.const 0)).toData.toBits := by
  rw [collapse, init, contents_listBits, zeroBits,
    iterate_terms ts (.const 0) _ (forest_length_ge ts), pairSnd_pair]

theorem eval_accumulate (ts : List Term) (acc : Term) (env : ℕ → ℝ) :
    (accumulate ts acc).eval env = acc.eval env + (Term.sumSquares ts).eval env := by
  induction ts generalizing acc with
  | nil => simp [accumulate, Term.sumSquares, Term.eval]
  | cons t ts ih =>
      change (accumulate ts (.add t.square acc)).eval env = _
      rw [ih]
      simp only [Term.sumSquares, Term.square, Term.eval]
      ring

/-- The accumulated equation vanishes exactly when every input equation vanishes. -/
theorem accumulate_zero_iff (ts : List Term) (env : ℕ → ℝ) :
    (accumulate ts (.const 0)).eval env = 0 ↔ ∀ t ∈ ts, t.eval env = 0 := by
  rw [eval_accumulate]
  simpa only [Term.eval, Int.cast_zero, zero_add] using Term.eval_sumSquares_eq_zero_iff ts env

end LeanCanny.ETR.SumSquares

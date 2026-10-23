/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationEncoding
public import LeanCanny.Computation.PolyTimeCaptured

/-!
# A polynomial-time equation-list masking pass

The input is `pair factor encodedTermList`. The loop retains the factor once,
consumes serialized terms, and appends their products to a forest accumulator.
Each step adds at most `factor.length + 10` bits to the complete paired state.
This bounds every iteration on all strings, not only on valid term lists.
-/

@[expose] public section

namespace LeanCanny.ETR.EquationMask

open LeanCanny.Encoding.Brackets

def step (state : List Bool) : List Bool :=
  let factor := pairFst state
  let work := pairSnd state
  let todo := pairFst work
  if todo = [] then state
  else pair factor (pair (afterNode todo)
    (pairSnd work ++ Codec.taggedTwo 3 factor (firstNode todo)))

theorem step_mem_FP : step ∈ FP := by
  have ht := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have ha := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hr := mem_FP_comp ht afterNode_mem_FP
  have hh := mem_FP_comp ht firstNode_mem_FP
  have hm := Codec.taggedTwo_mem_FP 3 pairFst_mem_FP hh
  have hn := mem_FP_pair pairFst_mem_FP (mem_FP_pair hr (appendFn_mem_FP ha hm))
  have he := stringEq_fppred ht (constFn_mem_FP [])
  refine mem_FP_of_eq (he.ite_mem_FP id_mem_FP hn) (fun state => ?_)
  simp only [step, Function.comp_apply, id_eq]

theorem step_pair_exists (factor todo acc : List Bool) :
    ∃ todo' acc', step (pair factor (pair todo acc)) = pair factor (pair todo' acc') := by
  by_cases he : todo = []
  · exact ⟨todo, acc, by simp [step, he]⟩
  · exact ⟨afterNode todo, acc ++ Codec.taggedTwo 3 factor (firstNode todo), by simp [step, he]⟩

theorem iterate_pair_exists (n : ℕ) (factor todo acc : List Bool) :
    ∃ todo' acc', step^[n] (pair factor (pair todo acc)) = pair factor (pair todo' acc') := by
  induction n with
  | zero => exact ⟨todo, acc, rfl⟩
  | succ n ih =>
      obtain ⟨todo', acc', hi⟩ := ih
      rw [Function.iterate_succ_apply', hi]
      exact step_pair_exists factor todo' acc'

theorem step_pair_length_le (factor todo acc : List Bool) :
    (step (pair factor (pair todo acc))).length ≤
      (pair factor (pair todo acc)).length + factor.length + 10 := by
  have hp : (firstNode todo).length + (afterNode todo).length = todo.length := by
    have hh := congrArg List.length (List.take_append_drop (nodeLength todo) todo)
    simpa only [List.length_append, firstNode, afterNode] using hh
  by_cases he : todo = []
  · simp [step, he]
    omega
  · simp only [step, pairFst_pair, pairSnd_pair, ite_eq_right he, pair_length,
      List.length_append, SumSquares.taggedTwo_length]
    omega

theorem iterate_pair_length_le (n : ℕ) (factor todo acc : List Bool) :
    (step^[n] (pair factor (pair todo acc))).length ≤
      (pair factor (pair todo acc)).length + n * (factor.length + 10) := by
  induction n with
  | zero => simp
  | succ n ih =>
      obtain ⟨todo', acc', hi⟩ := iterate_pair_exists n factor todo acc
      have hs := step_pair_length_le factor todo' acc'
      rw [hi] at ih
      rw [Function.iterate_succ_apply', hi]
      simp only [Nat.add_mul, Nat.one_mul]
      omega

def ruler (input : List Bool) : List Bool := contents (pairSnd input)

def init (input : List Bool) : List Bool := pair (pairFst input) (pair (ruler input) [])

def mask (input : List Bool) : List Bool :=
  wrap (pairSnd (pairSnd (step^[(ruler input).length] (init input))))

theorem mask_mem_FP : mask ∈ FP := by
  have hr : ruler ∈ FP := mem_FP_comp pairSnd_mem_FP contents_mem_FP
  let next := fun factor work =>
    if pairFst work = [] then work else pair (afterNode (pairFst work))
      (pairSnd work ++ Codec.taggedTwo 3 factor (firstNode (pairFst work)))
  have hloop := CapturedIteration.mem_FP next step_mem_FP pairFst_mem_FP
    (mem_FP_pair hr (constFn_mem_FP [])) (UnaryFn.length hr)
    (fun factor work => by
      dsimp only [step, next]
      simp only [pairFst_pair, pairSnd_pair]
      split_ifs <;> rfl)
    (pairFst_mem_FP.polyBounded_length.add (.const 12)) (fun z work => by
      have hp := CapturedIteration.pair_components_length_le work
      have hnode : (firstNode (pairFst work)).length + (afterNode (pairFst work)).length =
          (pairFst work).length := by
        simpa only [List.length_append, firstNode, afterNode] using
          congrArg List.length (List.take_append_drop (nodeLength (pairFst work)) (pairFst work))
      simp only [Turing.MultiTapeTM.encBits_apply]
      dsimp only [next]
      split_ifs
      · omega
      · simp only [pair_length, List.length_append, SumSquares.taggedTwo_length]
        omega)
  have ho := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) wrap_mem_FP
  exact mem_FP_of_eq (mem_FP_comp hloop ho) (fun _ => rfl)

theorem step_term_cons (factor t : Term) (ts : List Term) (acc : List Bool) :
    step (pair factor.toData.toBits (pair (SumSquares.forest (t :: ts)) acc)) =
      pair factor.toData.toBits
        (pair (SumSquares.forest ts) (acc ++ (Term.mul factor t).toData.toBits)) := by
  have hn : SumSquares.forest (t :: ts) ≠ [] := by
    have hl := SumSquares.forest_length_ge (t :: ts)
    intro he
    rw [he] at hl
    simp at hl
  rw [step, pairFst_pair, pairSnd_pair, pairFst_pair, pairSnd_pair, ite_eq_right hn,
    SumSquares.forest_cons, afterNode_toBits_append, firstNode_toBits_append, ← Term.mul_toBits]

theorem iterate_terms (factor : Term) (ts : List Term) (acc : List Bool)
    (n : ℕ) (hn : ts.length ≤ n) :
    step^[n] (pair factor.toData.toBits (pair (SumSquares.forest ts) acc)) =
      pair factor.toData.toBits (pair [] (acc ++ SumSquares.forest (ts.map (Term.mul factor)))) := by
  induction ts generalizing acc n with
  | nil =>
      induction n with
      | zero => simp [SumSquares.forest]
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih (by simp)]
          simp [step, SumSquares.forest]
  | cons t ts ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          rw [Function.iterate_succ_apply, step_term_cons]
          simpa only [List.map_cons, SumSquares.forest_cons, List.append_assoc] using
            ih (acc ++ (Term.mul factor t).toData.toBits) n
              (by simp only [List.length_cons] at hn; omega)

theorem wrap_forest (ts : List Term) : wrap (SumSquares.forest ts) = SumSquares.listBits ts := by
  simp only [SumSquares.forest, SumSquares.listBits, Data.toBits_l, List.map_map,
    Function.comp_def, wrap]

/-- Exact agreement with the typed equation-list map, preserving its order. -/
theorem mask_pair (factor : Term) (ts : List Term) :
    mask (pair factor.toData.toBits (SumSquares.listBits ts)) =
      SumSquares.listBits (ts.map (Term.mul factor)) := by
  simp only [mask, init, ruler, pairFst_pair, pairSnd_pair, SumSquares.contents_listBits]
  rw [iterate_terms factor ts [] _ (SumSquares.forest_length_ge ts)]
  simp only [pairSnd_pair, List.nil_append, wrap_forest]

end LeanCanny.ETR.EquationMask

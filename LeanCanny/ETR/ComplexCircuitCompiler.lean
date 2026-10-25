/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexGateEncoding
public import LeanCanny.Computation.PolyTimeIteration

/-! # A native polynomial-time complex-network equation compiler

The loop consumes encoded gates and appends their real equations. Its input
suffix never grows, so the gate writer's polynomial output bound also bounds
the complete accumulator throughout every iteration, including malformed input.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open LeanCanny.Encoding.Brackets

def step (state : List Bool) : List Bool :=
  let todo := pairFst state
  if todo = [] then state
  else pair (afterNode todo) (pairSnd state ++ gateBits (firstNode todo))

theorem step_mem_FP : step ∈ FP := by
  have ht := mem_FP_comp pairFst_mem_FP firstNode_mem_FP
  have hr := mem_FP_comp pairFst_mem_FP afterNode_mem_FP
  have hg := mem_FP_comp ht gateBits_mem_FP
  have he := stringEq_fppred pairFst_mem_FP (constFn_mem_FP [])
  have h := he.ite_mem_FP id_mem_FP (mem_FP_pair hr (appendFn_mem_FP pairSnd_mem_FP hg))
  apply mem_FP_of_eq h
  intro state
  simp only [step, Function.comp_apply, id_eq]

private theorem split_length (todo : List Bool) :
    (firstNode todo).length + (afterNode todo).length = todo.length := by
  simpa only [List.length_append, firstNode, afterNode] using
    congrArg List.length (List.take_append_drop (nodeLength todo) todo)

private theorem iterate_pair_bounds (a d : ℕ)
    (hg : ∀ bits, (gateBits bits).length ≤ a * (bits.length + 1) ^ d)
    (n : ℕ) (todo acc : List Bool) :
    ∃ todo' acc', step^[n] (pair todo acc) = pair todo' acc' ∧ todo'.length ≤ todo.length ∧
      acc'.length ≤ acc.length + n * (a * (todo.length + 1) ^ d) := by
  induction n with
  | zero => exact ⟨todo, acc, rfl, le_rfl, by simp⟩
  | succ n ih =>
    obtain ⟨t, s, he, ht, hs⟩ := ih
    have hn := split_length t
    by_cases hz : t = []
    · refine ⟨t, s, ?_, ht, ?_⟩
      · rw [Function.iterate_succ_apply', he]
        simp only [step, pairFst_pair, hz, ite_true]
      · rw [Nat.succ_mul]
        omega
    · have hnode : (firstNode t).length ≤ todo.length := by omega
      have hgate := (hg (firstNode t)).trans
        (Nat.mul_le_mul_left a (Nat.pow_le_pow_left (Nat.add_le_add_right hnode 1) d))
      refine ⟨afterNode t, s ++ gateBits (firstNode t), ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', he]
        simp only [step, pairFst_pair, pairSnd_pair, ite_eq_right hz]
      · omega
      · simp only [List.length_append, Nat.succ_mul]
        omega

def init (bits : List Bool) : List Bool := pair (contents bits) []
def compile (bits : List Bool) : List Bool := wrap (pairSnd (step^[(contents bits).length] (init bits)))

theorem compile_mem_FP : compile ∈ FP := by
  obtain ⟨a, d, hg⟩ := gateBits_mem_FP.polyBounded_length.exists_le
  let B := fun L => 2 * L + 2 + L * (a * (L + 1) ^ d)
  have hB : PolyBound B :=
    (((PolyBound.const 2).mul PolyBound.id).add (PolyBound.const 2)).add
      (PolyBound.id.mul ((PolyBound.const a).mul ((PolyBound.id.add (PolyBound.const 1)).pow d)))
  have hi : init ∈ FP := mem_FP_pair contents_mem_FP (constFn_mem_FP [])
  have hloop := iterate_mem_FP_of_polyBound step_mem_FP hi contents_mem_FP hB (fun bits n hn => by
    obtain ⟨t, s, he, ht, hs⟩ := iterate_pair_bounds a d hg n (contents bits) []
    change (step^[n] (pair (contents bits) [])).length ≤ B bits.length
    rw [he, pair_length]
    have hc : (contents bits).length ≤ bits.length := by
      simp only [contents, List.length_take, List.length_drop]
      omega
    have hp := Nat.mul_le_mul_left a (Nat.pow_le_pow_left (Nat.add_le_add_right hc 1) d)
    have hm := Nat.mul_le_mul (hn.trans hc) hp
    simp only [List.length_nil, Nat.zero_add] at hs
    dsimp only [B]
    omega)
  have h := mem_FP_comp (mem_FP_comp hloop pairSnd_mem_FP) wrap_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem step_gate_cons (g : Gate) (gates : List Gate) (acc : List Bool) :
    step (pair (forest (g :: gates)) acc) = pair (forest gates) (acc ++ SumSquares.forest g.equations) := by
  have hn : forest (g :: gates) ≠ [] := by
    have hl := forest_length_ge (g :: gates)
    intro he
    rw [he] at hl
    simp at hl
  rw [step, pairFst_pair, ite_eq_right hn, pairSnd_pair, forest_cons]
  change pair (afterNode (g.toData.toBits ++ forest gates))
    (acc ++ gateBits (firstNode (g.toData.toBits ++ forest gates))) = _
  rw [afterNode_toBits_append, firstNode_toBits_append]
  change pair (forest gates) (acc ++ gateBits g.encode) = _
  rw [gateBits_encode]

theorem real_forest_append (a b : List Term) :
    SumSquares.forest (a ++ b) = SumSquares.forest a ++ SumSquares.forest b := by
  simp only [SumSquares.forest, List.map_append, List.flatten_append]

theorem iterate_gates (gates : List Gate) (acc : List Bool) (n : ℕ) (hn : gates.length ≤ n) :
    step^[n] (pair (forest gates) acc) = pair [] (acc ++ SumSquares.forest (equations gates)) := by
  induction gates generalizing acc n with
  | nil =>
    induction n with
    | zero => simp [forest, equations, SumSquares.forest]
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by simp)]
      simp [step]
  | cons g gates ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      rw [Function.iterate_succ_apply, step_gate_cons]
      have h := ih (acc ++ SumSquares.forest g.equations) n (by simp only [List.length_cons] at hn; omega)
      simpa only [equations, List.flatMap_cons, real_forest_append, List.append_assoc] using h

theorem contents_encode (gates : List Gate) : contents (encode gates) = forest gates := by
  simp only [encode, contents_toBits, forest, List.map_map, Function.comp_def]
  rfl

theorem compile_encode (gates : List Gate) : compile (encode gates) = SumSquares.listBits (equations gates) := by
  rw [compile, init, contents_encode, iterate_gates gates [] _ (forest_length_ge gates), pairSnd_pair, List.nil_append]
  simp only [SumSquares.listBits, SumSquares.forest, Data.toBits_l, wrap, List.map_map, Function.comp_def]

theorem compile_encode_correct (gates : List Gate) :
    compile (encode gates) ∈ EquationList.language ↔ Satisfiable gates := by
  have hi : Function.Injective SumSquares.listBits := by
    intro a b h
    exact (List.map_injective_iff.mpr Term.toData_injective)
      (Data.l.inj (Data.toBits_injective h))
  rw [compile_encode, satisfiable_iff_real]
  simp only [EquationList.language, Set.mem_ofPred_eq, hi.eq_iff]
  constructor
  · rintro ⟨ts, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, rfl, h⟩

end LeanCanny.ETR.ComplexCircuit

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuitCompiler
public import LeanCanny.ETR.ComplexPowerSize

/-! # Polynomial-time substitution of complex gates

A gate may be replaced by a finite network. The total scanner is polynomial
time whenever its local writer is polynomial time, including on malformed
inputs. Semantic agreement requires only agreement on individual gate codes.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Transform
open LeanCanny.Encoding.Brackets

def step (writer : List Bool → List Bool) (state : List Bool) : List Bool :=
  let todo := pairFst state
  if todo = [] then state else pair (afterNode todo) (pairSnd state ++ writer (firstNode todo))

theorem step_mem_FP {writer : List Bool → List Bool} (hw : writer ∈ FP) : step writer ∈ FP := by
  have ht := mem_FP_comp pairFst_mem_FP firstNode_mem_FP
  have hr := mem_FP_comp pairFst_mem_FP afterNode_mem_FP
  have hg := mem_FP_comp ht hw
  have h := (stringEq_fppred pairFst_mem_FP (constFn_mem_FP [])).ite_mem_FP id_mem_FP
    (mem_FP_pair hr (appendFn_mem_FP pairSnd_mem_FP hg))
  exact mem_FP_of_eq h (fun _ => rfl)

private theorem iterate_bounds (writer : List Bool → List Bool) (a d : ℕ)
    (hg : ∀ bits, (writer bits).length ≤ a * (bits.length + 1) ^ d)
    (n : ℕ) (todo acc : List Bool) :
    ∃ todo' acc', (step writer)^[n] (pair todo acc) = pair todo' acc' ∧ todo'.length ≤ todo.length ∧
      acc'.length ≤ acc.length + n * (a * (todo.length + 1) ^ d) := by
  induction n with
  | zero => exact ⟨todo, acc, rfl, le_rfl, by simp⟩
  | succ n ih =>
    obtain ⟨t, s, he, ht, hs⟩ := ih
    have hn : (firstNode t).length + (afterNode t).length = t.length := by
      simpa only [List.length_append, firstNode, afterNode] using
        congrArg List.length (List.take_append_drop (nodeLength t) t)
    by_cases hz : t = []
    · refine ⟨t, s, ?_, ht, ?_⟩
      · rw [Function.iterate_succ_apply', he]
        simp only [step, pairFst_pair, hz, ite_true]
      · rw [Nat.succ_mul]; omega
    · have hnode : (firstNode t).length ≤ todo.length := by omega
      have hgate := (hg (firstNode t)).trans
        (Nat.mul_le_mul_left a (Nat.pow_le_pow_left (Nat.add_le_add_right hnode 1) d))
      refine ⟨afterNode t, s ++ writer (firstNode t), ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', he]
        simp only [step, pairFst_pair, pairSnd_pair, ite_eq_right hz]
      · omega
      · simp only [List.length_append, Nat.succ_mul]; omega

def run (writer : List Bool → List Bool) (bits : List Bool) : List Bool :=
  wrap (pairSnd ((step writer)^[(contents bits).length] (pair (contents bits) [])))

theorem run_mem_FP {writer : List Bool → List Bool} (hw : writer ∈ FP) : run writer ∈ FP := by
  obtain ⟨a, d, hg⟩ := hw.polyBounded_length.exists_le
  let B := fun L => 2 * L + 2 + L * (a * (L + 1) ^ d)
  have hB : PolyBound B :=
    (((PolyBound.const 2).mul PolyBound.id).add (PolyBound.const 2)).add
      (PolyBound.id.mul ((PolyBound.const a).mul ((PolyBound.id.add (PolyBound.const 1)).pow d)))
  have hloop := iterate_mem_FP_of_polyBound (step_mem_FP hw)
    (mem_FP_pair contents_mem_FP (constFn_mem_FP [])) contents_mem_FP hB (fun bits n hn => by
      obtain ⟨t, s, he, ht, hs⟩ := iterate_bounds writer a d hg n (contents bits) []
      rw [he, pair_length]
      have hc : (contents bits).length ≤ bits.length := by
        simp only [contents, List.length_take, List.length_drop]; omega
      have hp := Nat.mul_le_mul_left a (Nat.pow_le_pow_left (Nat.add_le_add_right hc 1) d)
      have hm := Nat.mul_le_mul (hn.trans hc) hp
      simp only [List.length_nil, Nat.zero_add] at hs
      dsimp only [B]
      omega)
  exact mem_FP_of_eq (mem_FP_comp (mem_FP_comp hloop pairSnd_mem_FP) wrap_mem_FP) (fun _ => rfl)

theorem run_encode (writer : List Bool → List Bool) (replace : Gate → List Gate)
    (hw : ∀ g, writer g.encode = forest (replace g)) (gs : List Gate) :
    run writer (encode gs) = encode (gs.flatMap replace) := by
  have hstep (g : Gate) (tail : List Gate) (acc : List Bool) :
      step writer (pair (forest (g :: tail)) acc) = pair (forest tail) (acc ++ forest (replace g)) := by
    have hn : forest (g :: tail) ≠ [] := by
      have hl := forest_length_ge (g :: tail)
      intro he; rw [he] at hl; simp at hl
    rw [step, pairFst_pair, ite_eq_right hn, pairSnd_pair, forest_cons]
    change pair (afterNode (g.toData.toBits ++ forest tail))
      (acc ++ writer (firstNode (g.toData.toBits ++ forest tail))) = _
    rw [afterNode_toBits_append, firstNode_toBits_append]
    exact congrArg (pair (forest tail)) (congrArg (acc ++ ·) (hw g))
  have hit : ∀ (tail : List Gate) (acc : List Bool) (n : ℕ), tail.length ≤ n →
      (step writer)^[n] (pair (forest tail) acc) = pair [] (acc ++ forest (tail.flatMap replace)) := by
    intro tail
    induction tail with
    | nil =>
      intro acc n hn
      induction n with
      | zero => simp [forest]
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih (by simp)]
        simp [step]
    | cons g tail ih =>
      intro acc n hn
      cases n with
      | zero => simp at hn
      | succ n =>
        rw [Function.iterate_succ_apply, hstep]
        have h := ih (acc ++ forest (replace g)) n (by simp only [List.length_cons] at hn; omega)
        simpa only [List.flatMap_cons, forest_append, List.append_assoc] using h
  rw [run, contents_encode, hit gs [] _ (forest_length_ge gs), pairSnd_pair, List.nil_append]
  exact (encode_eq_wrap _).symm

end LeanCanny.ETR.ComplexCircuit.Transform

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuitTransform

/-! # Gate substitution with a captured query parameter

The local writer receives both a fixed parameter word and the current encoded
gate. The native captured loop bounds every intermediate accumulator on all
strings. This supports fresh-wire offsets that vary with the input query.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.CapturedTransform
open LeanCanny.Encoding.Brackets Turing.MultiTapeTM

def step (writer : List Bool → List Bool) (par state : List Bool) : List Bool :=
  Transform.step (fun node => writer (pair par node)) state

def rawStep (writer : List Bool → List Bool) (packet : List Bool) : List Bool :=
  let par := pairFst packet
  let state := pairSnd packet
  let todo := pairFst state
  if todo = [] then state else pair (afterNode todo) (pairSnd state ++ writer (pair par (firstNode todo)))

theorem rawStep_mem_FP {writer : List Bool → List Bool} (hw : writer ∈ FP) : rawStep writer ∈ FP := by
  have hs := pairSnd_mem_FP
  have ht := mem_FP_comp (f := pairSnd) (g := pairFst) hs pairFst_mem_FP
  have hn := mem_FP_comp ht firstNode_mem_FP
  have hr := mem_FP_comp ht afterNode_mem_FP
  have ha := mem_FP_comp (f := pairSnd) (g := pairSnd) hs pairSnd_mem_FP
  have hg := mem_FP_comp (mem_FP_pair pairFst_mem_FP hn) hw
  exact mem_FP_of_eq ((stringEq_fppred ht (constFn_mem_FP [])).ite_mem_FP hs
    (mem_FP_pair hr (appendFn_mem_FP ha hg))) (fun _ => rfl)

theorem step_computable {writer : List Bool → List Bool} (hw : writer ∈ FP) :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool => step writer p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hpair := pair_computable (ComputableTidilyInPolyTime.fst encBits encBits)
    (ComputableTidilyInPolyTime.snd encBits encBits)
  apply ((FP.computable (rawStep_mem_FP hw)).comp hpair).of_enc_eq
  intro p
  simp only [encBits_apply, Function.comp_apply, rawStep, pairFst_pair, pairSnd_pair, step, Transform.step]

private theorem iterate_bounds (writer : List Bool → List Bool) (a d : ℕ)
    (hg : ∀ bits, (writer bits).length ≤ a * (bits.length + 1) ^ d)
    (par : List Bool) (n : ℕ) (todo acc : List Bool) :
    ∃ todo' acc', (step writer par)^[n] (pair todo acc) = pair todo' acc' ∧ todo'.length ≤ todo.length ∧
      acc'.length ≤ acc.length + n * (a * (2 * par.length + todo.length + 3) ^ d) := by
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
        simp only [step, Transform.step, pairFst_pair, hz, ite_true]
      · rw [Nat.succ_mul]; omega
    · have hnode : (firstNode t).length ≤ todo.length := by omega
      have hlen : (pair par (firstNode t)).length + 1 ≤ 2 * par.length + todo.length + 3 := by
        rw [pair_length]; omega
      have hgate := (hg (pair par (firstNode t))).trans
        (Nat.mul_le_mul_left a (Nat.pow_le_pow_left hlen d))
      refine ⟨afterNode t, s ++ writer (pair par (firstNode t)), ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', he]
        simp only [step, Transform.step, pairFst_pair, pairSnd_pair, ite_eq_right hz]
      · omega
      · simp only [List.length_append]
        rw [Nat.succ_mul]
        omega

def run (writer : List Bool → List Bool) (packet : List Bool) : List Bool :=
  Transform.run (fun node => writer (pair (pairFst packet) node)) (pairSnd packet)

theorem run_mem_FP {writer : List Bool → List Bool} (hw : writer ∈ FP) : run writer ∈ FP := by
  obtain ⟨a, d, hg⟩ := hw.polyBounded_length.exists_le
  let B := fun L => 2 * L + 2 + L * (a * (3 * L + 3) ^ d)
  have hB : PolyBound B :=
    (((PolyBound.const 2).mul PolyBound.id).add (PolyBound.const 2)).add
      (PolyBound.id.mul ((PolyBound.const a).mul
        ((((PolyBound.const 3).mul PolyBound.id).add (PolyBound.const 3)).pow d)))
  have hr := mem_FP_comp (f := pairSnd) (g := contents) pairSnd_mem_FP contents_mem_FP
  have hi := mem_FP_pair hr (constFn_mem_FP [])
  have hloop := ComputableTidilyInPolyTime.iterateWith pairFst_mem_FP
    (ComputableTidilyInPolyTime.length_bits.comp hr) hi (step_computable hw)
    (hB.polyBounded (fun z : List Bool => z.length)) (fun bits n hn => by
      obtain ⟨t, s, he, ht, hs⟩ := iterate_bounds writer a d hg (pairFst bits) n (contents (pairSnd bits)) []
      change ((step writer (pairFst bits))^[n] (pair (contents (pairSnd bits)) [])).length ≤ B bits.length
      rw [he, pair_length]
      have hp := pairFst_length_le bits
      have hq := pairSnd_length_le bits
      have hc : (contents (pairSnd bits)).length ≤ (pairSnd bits).length := by
        simp only [contents, List.length_take, List.length_drop]; omega
      have hsize : 2 * (pairFst bits).length + (contents (pairSnd bits)).length + 3 ≤ 3 * bits.length + 3 := by omega
      have hpow := Nat.mul_le_mul_left a (Nat.pow_le_pow_left hsize d)
      have hm := Nat.mul_le_mul (hn.trans (hc.trans hq)) hpow
      simp only [List.length_nil, Nat.zero_add] at hs
      dsimp only [B]
      omega)
  have h := mem_FP_comp (mem_FP_comp hloop pairSnd_mem_FP) wrap_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem run_encode (writer : List Bool → List Bool) (par : List Bool) (replace : Gate → List Gate)
    (hw : ∀ g, writer (pair par g.encode) = forest (replace g)) (gs : List Gate) :
    run writer (pair par (encode gs)) = encode (gs.flatMap replace) := by
  simp only [run, pairFst_pair, pairSnd_pair]
  exact Transform.run_encode _ replace hw gs

end LeanCanny.ETR.ComplexCircuit.CapturedTransform

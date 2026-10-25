/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexTermBounds
public import LeanCanny.ETR.TermView

/-! # A native polynomial-time source-circuit compiler

Validation supplies a total term view on every bitstring. A fixed number of
stack steps, linear in its literal syntax length, generates the exact shared
circuit. The full intermediate state has a quadratic encoded-length bound.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Source.Machine
open LeanCanny.Encoding LeanCanny.Encoding.Brackets

def initBits (bits : List Bool) : List Bool :=
  let source := TermView.normalize bits
  pair (pair (false :: source) []) (pair [] (pair (List.replicate source.length true) []))

def ruler (bits : List Bool) : List Bool := TermView.normalize bits ++ TermView.normalize bits
def runBits (bits : List Bool) : List Bool := stepBits^[(ruler bits).length] (initBits bits)
def compile (bits : List Bool) : List Bool := wrap (resultBits (runBits bits))
def outputIndex (bits : List Bool) : ℕ := (pairFst (valuesBits (runBits bits))).length
def nextIndex (bits : List Bool) : ℕ := (counterBits (runBits bits)).length

theorem initBits_mem_FP : initBits ∈ FP := by
  have ht := mem_FP_pair (mem_FP_comp TermView.normalize_mem_FP (cons_mem_FP false)) (constFn_mem_FP [])
  have hn := (UnaryFn.length TermView.normalize_mem_FP).replicate_mem_FP true
  exact mem_FP_of_eq (mem_FP_pair ht (mem_FP_pair (constFn_mem_FP [])
    (mem_FP_pair hn (constFn_mem_FP [])))) (fun _ => rfl)

theorem initBits_eq (bits : List Bool) : initBits bits =
    (State.mk [.visit (TermView.term bits)] [] (TermView.term bits).toData.size []).encode := by
  simp only [initBits, TermView.normalize_eq_term, Data.length_toBits, State.encode,
    DynamicTreeFold.stackBits, Instruction.encode, forest_nil]

theorem iterate_stepBits_encode (s : State) (n : ℕ) : stepBits^[n] s.encode = (step^[n] s).encode := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, stepBits_encode, Function.iterate_succ_apply']

theorem runBits_eq (bits : List Bool) : runBits bits =
    (State.mk [] [output (TermView.term bits).toData.size (TermView.term bits)]
      ((TermView.term bits).toData.size + count (TermView.term bits))
      (gates (TermView.term bits).toData.size (TermView.term bits))).encode := by
  rw [runBits, initBits_eq, iterate_stepBits_encode]
  simp only [ruler, List.length_append, TermView.normalize_eq_term, Data.length_toBits, ← two_mul]
  rw [run_steps _ _ _ (work_le_dataSize _)]

theorem runBits_mem_FP : runBits ∈ FP := by
  let B := fun L => 10000 * (L + 11) ^ 2
  have hB : PolyBound B := (PolyBound.const 10000).mul ((PolyBound.id.add (PolyBound.const 11)).pow 2)
  have hr : ruler ∈ FP := appendFn_mem_FP TermView.normalize_mem_FP TermView.normalize_mem_FP
  apply iterate_mem_FP_of_polyBound stepBits_mem_FP initBits_mem_FP hr hB
  intro bits n hn
  rw [initBits_eq, iterate_stepBits_encode]
  have ht : (TermView.term bits).toData.size ≤ bits.length + 10 := by
    simpa only [TermView.normalize_eq_term, Data.length_toBits] using TermView.normalize_length_le bits
  have hn' : n ≤ 2 * (TermView.term bits).toData.size := by
    simpa only [ruler, List.length_append, TermView.normalize_eq_term, Data.length_toBits, ← two_mul] using hn
  have he := run_encode_length_le (TermView.term bits) (TermView.term bits).toData.size
    (2 * (TermView.term bits).toData.size) n hn'
  have hwidth : (TermView.term bits).toData.size + (TermView.term bits).toData.size +
      2 * (TermView.term bits).toData.size + 1 ≤ 4 * (bits.length + 11) := by omega
  apply he.trans
  calc
    _ ≤ 100 * (4 * (bits.length + 11)) ^ 2 := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hwidth 2)
    _ ≤ B bits.length := by dsimp only [B]; nlinarith [Nat.zero_le ((bits.length + 11) ^ 2)]

theorem compile_mem_FP : compile ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (mem_FP_comp runBits_mem_FP resultBits_mem_FP) wrap_mem_FP) (fun _ => rfl)

theorem outputIndex_unary : UnaryFn outputIndex :=
  (UnaryFn.length (mem_FP_comp (f := runBits) (g := fun s => pairFst (valuesBits s)) runBits_mem_FP
    (mem_FP_comp valuesBits_mem_FP pairFst_mem_FP))).of_eq (fun _ => rfl)

theorem nextIndex_unary : UnaryFn nextIndex :=
  (UnaryFn.length (mem_FP_comp (f := runBits) (g := counterBits) runBits_mem_FP counterBits_mem_FP)).of_eq (fun _ => rfl)

theorem compile_eq (bits : List Bool) :
    compile bits = encode (gates (TermView.term bits).toData.size (TermView.term bits)) := by
  rw [compile, runBits_eq]
  simp only [resultBits, State.encode, pairSnd_pair]
  exact (encode_eq_wrap _).symm

theorem outputIndex_eq (bits : List Bool) :
    outputIndex bits = output (TermView.term bits).toData.size (TermView.term bits) := by
  simp [outputIndex, runBits_eq, valuesBits, State.encode, DynamicTreeFold.stackBits]

theorem nextIndex_eq (bits : List Bool) :
    nextIndex bits = (TermView.term bits).toData.size + count (TermView.term bits) := by
  simp [nextIndex, runBits_eq, counterBits, State.encode]

theorem compile_toBits (t : Term) : compile t.toData.toBits = encode (gates t.toData.size t) := by
  simp only [compile_eq, TermView.term_toBits]

end LeanCanny.ETR.ComplexCircuit.Source.Machine

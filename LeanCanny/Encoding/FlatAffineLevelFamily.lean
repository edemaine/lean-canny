/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineLevelSymbolic
public import LeanCanny.Encoding.FlatAffineFullSourceContext
public import LeanCanny.Computation.SpaceFunctionRange

/-! # Shared emission of every ancestral level slot

All slots have a uniform length and fixed output offsets. Their programs
read the original ancestral ambient blocks directly; no earlier stage or
level program is duplicated inside a slot.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineLevelFamily
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation LeanCanny.Algebra MvPolynomial
open FlatAffineFullSourceTower (Inputs)
open LeanCanny.Encoding.Brackets
open scoped Classical

def stride (F : Inputs) (u : List Bool) : ℕ := 9 * FlatAffineFullSourceTower.arity F u + 10

def slotBase (F : Inputs) (base : List Bool → ℕ) (j : ℕ) (u : List Bool) : ℕ := base u + j * stride F u

def slot (F : Inputs) (base ancestor : List Bool → ℕ) (u : List Bool) (k j : ℕ) : AffineLevel.Inputs :=
  FlatAffineLevelProgram.inputs F (slotBase F base j) ancestor u k j

def slotProgram (F : Inputs) (base ancestor : List Bool → ℕ) (u : List Bool) (k j : ℕ) : List Operation :=
  AffineLevel.packedProgram (slot F base ancestor u k j)

def prefixProgram (F : Inputs) (base ancestor stage : List Bool → ℕ) (u : List Bool) : ℕ → List Operation
  | 0 => []
  | j + 1 => prefixProgram F base ancestor stage u j ++ slotProgram F base ancestor u (stage u) j

def prefixGates (F : Inputs) (base ancestor stage : List Bool → ℕ) (u : List Bool) (j : ℕ) : List Gate :=
  StraightLine.gates (base u) (prefixProgram F base ancestor stage u j)

def program (F : Inputs) (base ancestor stage : List Bool → ℕ) (u : List Bool) : List Operation :=
  prefixProgram F base ancestor stage u (FlatAffineFullSourceTower.arity F u)

def output (F : Inputs) (base : List Bool → ℕ) (u : List Bool) (j : ℕ) : ℕ :=
  slotBase F base j u + 9 * FlatAffineFullSourceTower.arity F u + 9

theorem slot_length (F : Inputs) (base ancestor : List Bool → ℕ) (u : List Bool) (k j : ℕ) :
    (slotProgram F base ancestor u k j).length = stride F u := AffineLevel.packed_length _

theorem prefix_length (F : Inputs) (base ancestor stage : List Bool → ℕ) (u : List Bool) (j : ℕ) :
    (prefixProgram F base ancestor stage u j).length = j * stride F u := by
  induction j with
  | zero => simp only [prefixProgram, List.length_nil, Nat.zero_mul]
  | succ j ih => rw [prefixProgram, List.length_append, slot_length, ih, Nat.succ_mul]

theorem program_length (F : Inputs) (base ancestor stage : List Bool → ℕ) (u : List Bool) :
    (program F base ancestor stage u).length = FlatAffineFullSourceTower.arity F u * stride F u := prefix_length ..

theorem gates_succ (F : Inputs) (base ancestor stage : List Bool → ℕ) (u : List Bool) (j : ℕ) :
    prefixGates F base ancestor stage u (j + 1) = prefixGates F base ancestor stage u j ++
      StraightLine.gates (slotBase F base j u) (slotProgram F base ancestor u (stage u) j) := by
  rw [prefixGates, prefixProgram, StraightLine.gates_append, prefix_length]
  rfl

theorem gates_range (F : Inputs) (base ancestor stage : List Bool → ℕ) (u : List Bool) (j : ℕ) :
    prefixGates F base ancestor stage u j = (List.range j).flatMap (fun i =>
      StraightLine.gates (slotBase F base i u) (slotProgram F base ancestor u (stage u) i)) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [gates_succ, ih, List.range_succ, List.flatMap_append]; simp

theorem output_eq_slot (F : Inputs) (base ancestor : List Bool → ℕ) (u : List Bool) (k j : ℕ) :
    output F base u j = AffineLevel.packedOutput (slot F base ancestor u k j) := by
  rw [AffineLevel.packed_output_eq]
  rfl

theorem prefix_wellFormed (F : Inputs) (base ancestor stage : List Bool → ℕ) (u : List Bool)
    (hb : ancestor u + (stage u + 1) * FlatAffineFullSourceTower.stageWidth F u ≤ base u) (j : ℕ) :
    StraightLine.WellFormed (base u) (prefixProgram F base ancestor stage u j) := by
  induction j with
  | zero => trivial
  | succ j ih =>
    rw [prefixProgram, StraightLine.wellFormed_append, prefix_length]
    refine ⟨ih, ?_⟩
    exact AffineLevel.packed_wellFormed _ (FlatAffineLevelProgram.valid F (slotBase F base j) ancestor u (stage u) j
      (hb.trans (Nat.le_add_right _ _)))

theorem wellFormed (F : Inputs) (base ancestor stage : List Bool → ℕ) (u : List Bool)
    (hb : ancestor u + (stage u + 1) * FlatAffineFullSourceTower.stageWidth F u ≤ base u) :
    StraightLine.WellFormed (base u) (program F base ancestor stage u) := prefix_wellFormed F base ancestor stage u hb _

private theorem inputs_comp (F : Inputs) (f : List Bool → List Bool) (b a : List Bool → ℕ)
    (q : List Bool) (k j : ℕ) :
    FlatAffineLevelProgram.inputs (FlatAffineFullSourceContext.comp F f) b a q k j =
      FlatAffineLevelRecord.fromRecord (b q) (a q) (FlatAffineFullSourceTower.arity F (f q)) (F.width (f q)) k
        (F.level (FlatAffineFullSourceTower.levelQuery (f q) k j)) := by
  simp only [FlatAffineLevelProgram.inputs, FlatAffineFullSourceContext.comp, Function.comp_apply,
    FlatAffineFullSourceContext.query_level]
  rfl

private def slotCode (F : Inputs) (base ancestor stage : List Bool → ℕ) (q : List Bool) : List Bool :=
  encode (StraightLine.gates (slotBase F base (pairSnd q).length (pairFst q))
    (slotProgram F base ancestor (pairFst q) (stage (pairFst q)) (pairSnd q).length))

private theorem slot_evaluator {F : Inputs} (h : F.Access) {base ancestor stage : List Bool → ℕ}
    (hb : UnaryFn base) (ha : UnaryFn ancestor) (hk : UnaryFn stage) : SpaceFunction (slotCode F base ancestor stage) := by
  have hi := UnaryFn.length pairSnd_mem_FP
  have hs : UnaryFn (stride F) := ((UnaryFn.const 9).mul (FlatAffineFullSourceTower.arity_unary h)).add (UnaryFn.const 10)
  have hbase := (hb.comp pairFst_mem_FP).add (hi.mul (hs.comp pairFst_mem_FP))
  have H := FlatAffineLevelProgram.encode_evaluator (FlatAffineFullSourceContext.access h pairFst_mem_FP)
    hbase (ha.comp pairFst_mem_FP) (hk.comp pairFst_mem_FP) (BinaryFn.ofUnary hi)
  apply H.congr
  funext q
  simp only [FlatAffineLevelProgram.program, inputs_comp, slotCode, slotProgram, slot]
  rfl

theorem encode_evaluator {F : Inputs} (h : F.Access) {base ancestor stage : List Bool → ℕ}
    (hb : UnaryFn base) (ha : UnaryFn ancestor) (hk : UnaryFn stage) :
    SpaceFunction (fun u => encode (StraightLine.gates (base u) (program F base ancestor stage u))) := by
  have H := (((slot_evaluator h hb ha hk).postcompose contents contents_mem_FP).flatMap_unary
    (FlatAffineFullSourceTower.arity_unary h)).postcompose wrap wrap_mem_FP
  apply H.congr
  funext u
  simp only [Function.comp_apply, slotCode, contents_encode, pairFst_pair, pairSnd_pair, List.length_replicate]
  rw [encode_eq_wrap]
  change _ = wrap (LeanCanny.ETR.ComplexCircuit.forest (prefixGates F base ancestor stage u (FlatAffineFullSourceTower.arity F u)))
  rw [gates_range]
  simp only [LeanCanny.ETR.ComplexCircuit.forest, List.map_flatMap, List.flatten_eq_flatMap, List.flatMap_assoc]

theorem stride_unary {F : Inputs} (h : F.source.PolyTime) : UnaryFn (stride F) :=
  ((UnaryFn.const 9).mul (h.dim.add (UnaryFn.const 4))).add (UnaryFn.const 10)

theorem length_unary {F : Inputs} (h : F.source.PolyTime) (base ancestor stage : List Bool → ℕ) :
    UnaryFn (fun u => (program F base ancestor stage u).length) :=
  ((h.dim.add (UnaryFn.const 4)).mul (stride_unary h)).of_eq (fun _ => (program_length ..).symm)

theorem output_unary {F : Inputs} (h : F.source.PolyTime) {base : List Bool → ℕ} (hb : UnaryFn base) :
    UnaryFn (fun q => output F base (pairFst q) (pairSnd q).length) :=
  ((((hb.comp pairFst_mem_FP).add ((UnaryFn.length pairSnd_mem_FP).mul ((stride_unary h).comp pairFst_mem_FP))).add
    ((UnaryFn.const 9).mul ((h.dim.add (UnaryFn.const 4)).comp pairFst_mem_FP))).add (UnaryFn.const 9)).of_eq (fun _ => rfl)

end LeanCanny.Encoding.FlatAffineLevelFamily

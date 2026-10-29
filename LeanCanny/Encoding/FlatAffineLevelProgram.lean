/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineLevelRecord
public import LeanCanny.ETR.ComplexAffineLevelPacked

/-! # Capturing actual ancestral affine levels

The charged tower reader supplies each original level record. A native writer
emits its constant, height, or midpoint computation with a uniform number of
operations and exactly the tower's clamped references.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineLevelProgram
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation LeanCanny.Algebra
open FlatAffineFullSourceTower (Inputs)
open LeanCanny.Encoding.Brackets
open scoped Classical BigOperators

def inputs (F : Inputs) (base ancestor : List Bool → ℕ) (u : List Bool) (k j : ℕ) : AffineLevel.Inputs :=
  FlatAffineLevelRecord.fromRecord (base u) (ancestor u) (FlatAffineFullSourceTower.arity F u) (F.width u) k
    (F.level (FlatAffineFullSourceTower.levelQuery u k j))

def program (F : Inputs) (base ancestor stage slot : List Bool → ℕ) (u : List Bool) : List Operation :=
  AffineLevel.packedProgram (inputs F base ancestor u (stage u) (slot u))

theorem length_program (F : Inputs) (base ancestor stage slot : List Bool → ℕ) (u : List Bool) :
    (program F base ancestor stage slot u).length = 9 * FlatAffineFullSourceTower.arity F u + 10 :=
  AffineLevel.packed_length _

theorem valid (F : Inputs) (base ancestor : List Bool → ℕ) (u : List Bool) (k j : ℕ)
    (hb : ancestor u + (k + 1) * FlatAffineFullSourceTower.stageWidth F u ≤ base u) :
    (inputs F base ancestor u k j).Valid := FlatAffineLevelRecord.valid _ _ _ _ _ _ hb

theorem wellFormed (F : Inputs) (base ancestor stage slot : List Bool → ℕ) (u : List Bool)
    (hb : ancestor u + (stage u + 1) * FlatAffineFullSourceTower.stageWidth F u ≤ base u) :
    StraightLine.WellFormed (base u) (program F base ancestor stage slot u) :=
  AffineLevel.packed_wellFormed _ (valid F base ancestor u _ _ hb)

theorem encode_evaluator {F : Inputs} (h : F.Access) {base ancestor stage slot : List Bool → ℕ}
    (hb : UnaryFn base) (ha : UnaryFn ancestor) (hk : UnaryFn stage) (hj : BinaryFn slot) :
    SpaceFunction (fun u => encode (StraightLine.gates (base u) (program F base ancestor stage slot u))) := by
  let read : List Bool → List Bool := fun u => F.level (FlatAffineFullSourceTower.levelQuery u (stage u) (slot u))
  have hquery := mem_FP_pair (mem_FP_pair id_mem_FP (BinaryFn.ofUnary hk).bits_mem_FP) hj.bits_mem_FP
  have hread : SpaceFunction read := h.level.precompose _ hquery
  let write : List Bool → List Bool := fun q => encode (AffineLevel.packedGates
    (FlatAffineLevelRecord.fromRecord (base (pairFst q)) (ancestor (pairFst q)) (FlatAffineFullSourceTower.arity F (pairFst q))
      (F.width (pairFst q)) (stage (pairFst q)) (pairSnd q)))
  have hwrite : write ∈ FP := AffineLevel.packed_encode_FP (FlatAffineLevelRecord.polyTime
    (hb.comp pairFst_mem_FP) (ha.comp pairFst_mem_FP) ((FlatAffineFullSourceTower.arity_unary h).comp pairFst_mem_FP)
    (h.width.comp pairFst_mem_FP) (hk.comp pairFst_mem_FP) pairSnd_mem_FP)
  have H := hread.withInput.postcompose write hwrite
  exact H.congr (funext fun u => by
    simp only [write, read, program, inputs, Function.comp_apply, pairFst_pair, pairSnd_pair]
    rfl)

theorem length_unary {F : Inputs} (h : F.Access) (base ancestor stage slot : List Bool → ℕ) :
    UnaryFn (fun u => (program F base ancestor stage slot u).length) :=
  (((UnaryFn.const 9).mul (FlatAffineFullSourceTower.arity_unary h)).add (UnaryFn.const 10)).of_eq (fun _ => (length_program ..).symm)

def output (F : Inputs) (base ancestor : List Bool → ℕ) (u : List Bool) (k j : ℕ) : ℕ :=
  AffineLevel.packedOutput (inputs F base ancestor u k j)

theorem output_eq (F : Inputs) (base ancestor : List Bool → ℕ) (u : List Bool) (k j : ℕ) :
    output F base ancestor u k j = base u + 9 * FlatAffineFullSourceTower.arity F u + 9 :=
  AffineLevel.packed_output_eq _

theorem output_unary {F : Inputs} (h : F.source.PolyTime) {base : List Bool → ℕ} (hb : UnaryFn base)
    (ancestor stage slot : List Bool → ℕ) : UnaryFn (fun u => output F base ancestor u (stage u) (slot u)) :=
  ((hb.add ((UnaryFn.const 9).mul (h.dim.add (UnaryFn.const 4)))).add (UnaryFn.const 9)).of_eq
    (fun u => (output_eq F base ancestor u (stage u) (slot u)).symm)

end LeanCanny.Encoding.FlatAffineLevelProgram

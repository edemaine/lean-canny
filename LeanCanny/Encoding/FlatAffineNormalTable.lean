/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineIntegerLiteral
public import LeanCanny.ETR.ComplexConstantTable

/-! # Capturing the actual signed affine normal records

A charged direction reader supplies one record. A polynomial-space writer
captures its entire normal matrix as shared binary integer constants, with
native length, reference bounds, and exact original-direction semantics.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineNormalTable
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation MvPolynomial
open FlatAffineFullSourceTower (Inputs)
open LeanCanny.Encoding.Brackets
open scoped Classical

def count (F : Inputs) (u : List Bool) : ℕ :=
  (FlatAffineFullSourceTower.arity F u + 1) * FlatAffineFullSourceTower.arity F u

def value (F : Inputs) (u : List Bool) (stage j : ℕ) : ℤ :=
  FlatAffineFullSourceTower.integer (F.width u) (F.direction (FlatAffineFullSourceTower.stage u stage)) j

def program (F : Inputs) (stage : List Bool → ℕ) (u : List Bool) : List Operation :=
  ConstantTable.program (count F u) (value F u (stage u))

def reference (F : Inputs) (base : List Bool → ℕ) (u : List Bool) (r i : ℕ) : ℕ :=
  base u + (r * FlatAffineFullSourceTower.arity F u + i)

theorem count_unary {F : Inputs} (h : F.source.PolyTime) : UnaryFn (count F) :=
  (((h.dim.add (UnaryFn.const 4)).add (UnaryFn.const 1)).mul (h.dim.add (UnaryFn.const 4))).of_eq (fun _ => rfl)

theorem length_program (F : Inputs) (stage : List Bool → ℕ) (u : List Bool) :
    (program F stage u).length = count F u := ConstantTable.program_length ..

theorem wellFormed (F : Inputs) (stage base : List Bool → ℕ) (u : List Bool) :
    StraightLine.WellFormed (base u) (program F stage u) := ConstantTable.wellFormed ..

theorem reference_lt (F : Inputs) (base : List Bool → ℕ) (u : List Bool)
    (r : Fin (FlatAffineFullSourceTower.arity F u + 1)) (i : Fin (FlatAffineFullSourceTower.arity F u)) :
    reference F base u r.val i.val < base u + count F u := by
  have hr := r.isLt
  have hi := i.isLt
  unfold reference count
  nlinarith

theorem normal_sound (F : Inputs) (stage base : List Bool → ℕ) (u : List Bool) (env : ℕ → ℂ)
    (hg : ∀ g ∈ StraightLine.gates (base u) (program F stage u), g.Holds env)
    (r : Fin (FlatAffineFullSourceTower.arity F u + 1)) (i : Fin (FlatAffineFullSourceTower.arity F u)) :
    env (reference F base u r.val i.val) = (FlatAffineFullSourceTower.direction F u (stage u) r i : ℂ) := by
  apply ConstantTable.sound (base u) (count F u) (value F u (stage u)) env hg
  have H := reference_lt F base u r i
  unfold reference at H
  omega

theorem normal_symbolic {σ : Type*} (F : Inputs) (stage base : List Bool → ℕ) (u : List Bool)
    (wire : ℕ → MvPolynomial σ ℤ)
    (r : Fin (FlatAffineFullSourceTower.arity F u + 1)) (i : Fin (FlatAffineFullSourceTower.arity F u)) :
    Differential.symbolicRun wire (base u) (program F stage u) (reference F base u r.val i.val) =
      C (FlatAffineFullSourceTower.direction F u (stage u) r i) := by
  apply ConstantTable.symbolic
  have H := reference_lt F base u r i
  unfold reference at H
  omega

theorem encode_evaluator {F : Inputs} (h : F.Access) {stage base : List Bool → ℕ}
    (hk : BinaryFn stage) (hb : UnaryFn base) :
    SpaceFunction (fun u => encode (StraightLine.gates (base u) (program F stage u))) := by
  let read : List Bool → List Bool := fun u => F.direction (FlatAffineFullSourceTower.stage u (stage u))
  have hread : SpaceFunction read := h.direction.precompose _ (mem_FP_pair id_mem_FP hk.bits_mem_FP)
  let write : List Bool → List Bool := fun q => encode (StraightLine.gates (base (pairFst q))
    (ConstantTable.program (count F (pairFst q))
      (fun j => FlatAffineFullSourceTower.integer (F.width (pairFst q)) (pairSnd q) j)))
  have hv := FlatAffineIntegerLiteral.literal_FP
    (h.width.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)) (UnaryFn.length pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have hwrite : write ∈ FP := ConstantTable.encode_FP (hb.comp pairFst_mem_FP) ((count_unary h.source).comp pairFst_mem_FP) hv
  have H := hread.withInput.postcompose write hwrite
  exact H.congr (funext fun u => by
    simp only [write, read, program, Function.comp_apply, pairFst_pair, pairSnd_pair]
    rfl)

end LeanCanny.Encoding.FlatAffineNormalTable

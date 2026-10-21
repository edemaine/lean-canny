/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzPSPACE
public import LeanCanny.Algebra.MatrixMomentSpaceEntries

/-!
# Trailing-block moments from space-bounded original entries

Every query determines a stage, trailing dimension, and moment exponent.
Vectors over an empty trailing block have no original-entry obligations, so
the semantic family and its access contract cover every binary context.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz.ModularAccess
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower
open Matrix

structure ControlsPolyTime {F : ModularFamily} (a : ModularAccess F) : Prop where
  dimension : a.access.dimension ∈ FP
  modulus : a.access.modulus ∈ FP

def stage (F : ModularFamily) (p : List Bool) : ℕ :=
  Nat.fromBitsLE (QueryBits.rowIndex p) / (F.dimension (pairFst p) + 1)

def trailingDimension (F : ModularFamily) (p : List Bool) : ℕ :=
  F.dimension (pairFst p) - stage F p - 1

def momentDegree (F : ModularFamily) (p : List Bool) : ℕ :=
  Nat.fromBitsLE (QueryBits.colIndex p) % (F.dimension (pairFst p) + 1) -
    (Nat.fromBitsLE (QueryBits.rowIndex p) % (F.dimension (pairFst p) + 1) + 1)

def momentFamily (F : ModularFamily) : MatrixMoment.ModularFamily where
  dimension := trailingDimension F
  modulus := fun p => F.modulus (pairFst p)
  exponent := momentDegree F
  row := fun p j => F.matrix (pairFst p)
    ⟨stage F p, by have hj := j.isLt; dsimp only [trailingDimension] at hj; omega⟩
    ⟨stage F p + 1 + j.val, by have hj := j.isLt; dsimp only [trailingDimension] at hj; omega⟩
  column := fun p i => F.matrix (pairFst p)
    ⟨stage F p + 1 + i.val, by have hi := i.isLt; dsimp only [trailingDimension] at hi; omega⟩
    ⟨stage F p, by have hi := i.isLt; dsimp only [trailingDimension] at hi; omega⟩
  matrix := fun p i j => F.matrix (pairFst p)
    ⟨stage F p + 1 + i.val, by have hi := i.isLt; dsimp only [trailingDimension] at hi; omega⟩
    ⟨stage F p + 1 + j.val, by have hj := j.isLt; dsimp only [trailingDimension] at hj; omega⟩
  modulus_ne_zero := fun p => F.modulus_ne_zero (pairFst p)

theorem sourceLayer_code {F : ModularFamily} (a : ModularAccess F) (p : List Bool) :
    QueryBits.sourceLayer a.access.dimension p = BinaryNatCode.encode (stage F p) := by
  rw [QueryBits.sourceLayer_eq_code]
  simp only [QueryBits.inputDimension, (a.correct (pairFst p)).dimension, QueryBits.code_value, stage]

theorem trailingDimension_code {F : ModularFamily} (a : ModularAccess F) (p : List Bool) :
    QueryBits.remaining a.access.dimension p = BinaryNatCode.encode (trailingDimension F p) := by
  rw [QueryBits.remaining_eq_code]
  simp only [QueryBits.inputDimension, (a.correct (pairFst p)).dimension, QueryBits.code_value,
    trailingDimension, stage]

theorem momentDegree_code {F : ModularFamily} (a : ModularAccess F) (p : List Bool) :
    QueryBits.momentExponent a.access.dimension p = BinaryNatCode.encode (momentDegree F p) := by
  rw [QueryBits.momentExponent_eq_code]
  simp only [QueryBits.inputDimension, (a.correct (pairFst p)).dimension, QueryBits.code_value, momentDegree]

def momentAccess {F : ModularFamily} (a : ModularAccess F) : MatrixMoment.ModularAccess (momentFamily F) where
  bits := EntryAccess.momentAccess a.access.dimension a.access.entry
  modulus := EntryAccess.childModulus a.access.modulus
  exponent := QueryBits.momentExponent a.access.dimension
  dimension_eq := trailingDimension_code a
  modulus_eq := fun p => (a.correct (pairFst p)).modulus
  exponent_eq := momentDegree_code a
  row_eq := by
    intro p j
    change Fin (trailingDimension F p) at j
    have hj := j.isLt
    have hs : stage F p < F.dimension (pairFst p) := by dsimp only [trailingDimension] at hj; omega
    have hv : stage F p + 1 + j.val < F.dimension (pairFst p) := by dsimp only [trailingDimension] at hj; omega
    simp only [EntryAccess.momentAccess, Function.comp_apply,
      EntryAccess.rowInput_code a.access.dimension p (stage F p) j.val (sourceLayer_code a p)]
    have h := (a.correct (pairFst p)).entry ⟨stage F p, hs⟩ ⟨stage F p + 1 + j.val, hv⟩
    simpa only [momentFamily] using h
  column_eq := by
    intro p i
    change Fin (trailingDimension F p) at i
    have hi := i.isLt
    have hs : stage F p < F.dimension (pairFst p) := by dsimp only [trailingDimension] at hi; omega
    have hv : stage F p + 1 + i.val < F.dimension (pairFst p) := by dsimp only [trailingDimension] at hi; omega
    simp only [EntryAccess.momentAccess, Function.comp_apply,
      EntryAccess.columnInput_code a.access.dimension p (stage F p) i.val (sourceLayer_code a p)]
    have h := (a.correct (pairFst p)).entry ⟨stage F p + 1 + i.val, hv⟩ ⟨stage F p, hs⟩
    simpa only [momentFamily] using h
  entry_eq := by
    intro p i j
    change Fin (trailingDimension F p) at i j
    have hi : stage F p + 1 + i.val < F.dimension (pairFst p) := by
      have h := i.isLt; dsimp only [trailingDimension] at h; omega
    have hj : stage F p + 1 + j.val < F.dimension (pairFst p) := by
      have h := j.isLt; dsimp only [trailingDimension] at h; omega
    simp only [EntryAccess.momentAccess, Function.comp_apply,
      EntryAccess.matrixInput_code a.access.dimension p (stage F p) i.val j.val (sourceLayer_code a p)]
    have h := (a.correct (pairFst p)).entry ⟨stage F p + 1 + i.val, hi⟩ ⟨stage F p + 1 + j.val, hj⟩
    simpa only [momentFamily] using h

theorem moment_controls {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) :
    a.momentAccess.ControlsPolyTime := by
  have hd := QueryBits.remaining_mem_FP ha.dimension
  have hm := EntryAccess.childModulus_mem_FP ha.modulus
  have he := QueryBits.momentExponent_mem_FP ha.dimension
  constructor
  · simpa only [momentAccess, EntryAccess.momentAccess] using hd
  · simpa only [momentAccess] using hm
  · simpa only [momentAccess] using he

theorem momentEvaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.access.entry) : SpaceFunction (momentFamily F).value := by
  have R := E.precompose (EntryAccess.rowInput a.access.dimension) (EntryAccess.rowInput_mem_FP ha.dimension)
  have C := E.precompose (EntryAccess.columnInput a.access.dimension) (EntryAccess.columnInput_mem_FP ha.dimension)
  have A := E.precompose (EntryAccess.matrixInput a.access.dimension) (EntryAccess.matrixInput_mem_FP ha.dimension)
  exact MatrixMoment.ModularAccess.evaluator a.momentAccess (moment_controls a ha) R C A

theorem moment_value_eq {F : ModularFamily} (p : List Bool)
    (hs : stage F p < F.dimension (pairFst p)) :
    (momentFamily F).value p = residueBits
      (borderMoment (fun j => principalBlock (F.matrix (pairFst p)) (stage F p) hs 0 j.succ)
        (fun i => principalBlock (F.matrix (pairFst p)) (stage F p) hs i.succ 0)
        ((principalBlock (F.matrix (pairFst p)) (stage F p) hs).submatrix Fin.succ Fin.succ)
        (momentDegree F p)) := by
  have hr : (momentFamily F).row p =
      fun j => principalBlock (F.matrix (pairFst p)) (stage F p) hs 0 j.succ := by
    funext j
    change Fin (F.dimension (pairFst p) - stage F p - 1) at j
    have hv : stage F p + 1 + j.val < F.dimension (pairFst p) := by have h := j.isLt; omega
    change F.matrix (pairFst p) ⟨stage F p, hs⟩ ⟨stage F p + 1 + j.val, hv⟩ =
      F.matrix (pairFst p) ⟨stage F p, hs⟩ ⟨stage F p + (j.val + 1), by omega⟩
    congr 1
    exact Fin.ext (by omega : stage F p + 1 + j.val = stage F p + (j.val + 1))
  have hc : (momentFamily F).column p =
      fun i => principalBlock (F.matrix (pairFst p)) (stage F p) hs i.succ 0 := by
    funext i
    change Fin (F.dimension (pairFst p) - stage F p - 1) at i
    have hv : stage F p + 1 + i.val < F.dimension (pairFst p) := by have h := i.isLt; omega
    change F.matrix (pairFst p) ⟨stage F p + 1 + i.val, hv⟩ ⟨stage F p, hs⟩ =
      F.matrix (pairFst p) ⟨stage F p + (i.val + 1), by omega⟩ ⟨stage F p, hs⟩
    congr 1
    exact Fin.ext (by omega : stage F p + 1 + i.val = stage F p + (i.val + 1))
  have hA : (momentFamily F).matrix p =
      (principalBlock (F.matrix (pairFst p)) (stage F p) hs).submatrix Fin.succ Fin.succ := by
    ext i j
    change Fin (F.dimension (pairFst p) - stage F p - 1) at i j
    have hi : stage F p + 1 + i.val < F.dimension (pairFst p) := by have h := i.isLt; omega
    have hj : stage F p + 1 + j.val < F.dimension (pairFst p) := by have h := j.isLt; omega
    change F.matrix (pairFst p) ⟨stage F p + 1 + i.val, hi⟩ ⟨stage F p + 1 + j.val, hj⟩ =
      F.matrix (pairFst p) ⟨stage F p + (i.val + 1), by omega⟩ ⟨stage F p + (j.val + 1), by omega⟩
    congr 1
    · exact Fin.ext (by omega : stage F p + 1 + i.val = stage F p + (i.val + 1))
    · exact Fin.ext (by omega : stage F p + 1 + j.val = stage F p + (j.val + 1))
  change residueBits ((momentFamily F).row p ⬝ᵥ ((momentFamily F).matrix p ^ momentDegree F p *ᵥ
    (momentFamily F).column p)) = _
  rw [hr, hc, hA]
  rfl

end LeanCanny.Algebra.Berkowitz.ModularAccess

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeProjectionRows
public import LeanCanny.ETR.TubeProjectionRowEncoding

/-! # Uniform polynomial-space projection coefficient residues

The FP row reader selects level or partial rows using the total row encoding.
Both derivative children and the final modular subtraction have complete space
certificates. Invalid row words select the level row; arbitrary exponent words
are interpreted blockwise without width aliasing in derivative queries.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeProjection

open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding TubeProjectionEncoding
open Algebra.MatrixPower

attribute [local irreducible] TubeDense.polynomial TubePolynomial.integerProjection TubeProjectionQuery.rowValue

noncomputable def decodedRow (base word : List Bool → List Bool) (c : List Bool) :
    TubePolynomial.ProjectionIndex (Fin (TubeDense.arity base c)) :=
  TubeProjectionRow.decode (TubeDense.arity base c) (TubeProjectionRow.index (TubeDense.arity base) word c)

noncomputable def value (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active word target modulus : List Bool → List Bool) : List Bool → List Bool :=
  TubeProjectionQuery.rowValue base W active target modulus (decodedRow base word)

theorem evaluator (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active word target modulus : List Bool → List Bool) (hb : base ∈ FP) (hW : UnaryFn W)
    (ha : active ∈ FP) (hw : word ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value base W active word target modulus) := by
  let n := TubeDense.arity base
  let k := TubeProjectionRow.index n word
  let r := fun c => TubeProjectionRow.selected (n c) (k c)
  have hn := TubeDense.arity_unary hb
  have hk := TubeProjectionRow.index_unary hn hw
  have hr := TubeProjectionRow.selected_unary hn hk
  let R := TubeProjectionQuery.partialEvaluator base W r active target modulus
    (fun c => TubeProjectionRow.point (n c) (k c)) hb hW hr ha ht hm
    (fun c => (TubeProjectionRow.point_index (n c) (k c)).symm)
  let L := TubeProjectionQuery.levelEvaluator base W active target modulus hb hW ha ht hm
  let P := fun c => TubeProjectionRow.Valid (n c) (k c)
  let E := SpaceFunction.branch (fun c => decide (P c)) (TubeProjectionRow.valid_fppred hn hk).flag_mem_FP R L
  refine E.congr (funext fun c => ?_)
  change (if decide (P c) then TubeProjectionQuery.rowValue base W active target modulus
    (fun c => some (TubeProjectionRow.point (n c) (k c))) c else
    TubeProjectionQuery.rowValue base W active target modulus (fun _ => none) c) = _
  unfold value TubeProjectionQuery.rowValue decodedRow
  by_cases hp : P c
  · simp only [hp, decide_true, ite_true]
    rw [TubeProjectionRow.decode, ite_eq_left hp]
  · simp only [hp, decide_false, Bool.false_eq_true, ite_false]
    rw [TubeProjectionRow.decode, ite_eq_right hp]

theorem decodedRow_of_code (base word : List Bool → List Bool) (c : List Bool)
    (j : TubePolynomial.ProjectionIndex (Fin (TubeDense.arity base c)))
    (hw : word c = BinaryNatCode.encode (TubeProjectionRow.code (TubeDense.arity base c) j)) : decodedRow base word c = j := by
  unfold decodedRow TubeProjectionRow.index
  rw [hw, BinaryNatCode.encode, Nat.fromBitsLE_bits, min_eq_left (TubeProjectionRow.code_lt _ j).le, TubeProjectionRow.decode_code]

end LeanCanny.ETR.TubeProjection

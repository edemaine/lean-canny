/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSelectorClosure
public import LeanCanny.Encoding.FrozenCoordinatePermutationInverseFP
/-! # The actual frozen sweep index has original-level space access -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSelectorSpace
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FrozenCoordinatePermutationBits.inverseReader maskWord

theorem inverse_evaluator {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP)
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val)) :
    SpaceFunction (fun q => BinaryNatCode.encode ((FlatAffineExceptionalOrderedRule.order F (input q)).symm (h (input q))).val) := by
  have HH : BinaryFn (fun q => (h (input q)).val) := hh.comp hi
  have HQ := (maskWord_space hF input hi).pairOutputs (SpaceFunction.ofFP _ HH.bits_mem_FP)
  apply (HQ.postcompose FrozenCoordinatePermutationBits.inverseReader FrozenCoordinatePermutationBits.inverseReader_FP).congr
  funext q
  simp only [Function.comp_apply]
  rw [maskWord_eq]
  exact FrozenCoordinatePermutationBits.inverse_reader_mask _ (h (input q))

theorem height_unary {F : Inputs} (hF : F.Access) (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val)) :
    UnaryFn (fun u => (h u).val) :=
  (UnaryFn.fromBitsLE_min hh.bits_mem_FP (FlatAffineFullSourceTower.arity_unary hF)).of_eq
    (fun u => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.min_eq_left (h u).isLt.le])
end LeanCanny.Encoding.FlatAffineExceptionalSelectorSpace

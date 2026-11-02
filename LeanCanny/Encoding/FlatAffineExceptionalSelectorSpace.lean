/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FrozenCoordinatePermutationCorrect
public import LeanCanny.Encoding.FlatAffineExceptionalRuleCellsSpace
public import LeanCanny.Computation.SpaceFunctionRange
/-! # Actual frozen-first selectors from charged original level flags -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSelectorSpace
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def flagQuery (F : Inputs) (input : List Bool → List Bool) (p : List Bool) :=
  FlatAffineFullSourceTower.levelQuery (input (pairFst p)) (F.depth (input (pairFst p))) (pairSnd p).length

theorem flagQuery_FP {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP) : flagQuery F input ∈ FP := by
  have HU : (fun p => input (pairFst p)) ∈ FP := mem_FP_comp pairFst_mem_FP hi
  have HK : BinaryFn (fun p => F.depth (input (pairFst p))) := (BinaryFn.ofUnary hF.depth).comp HU
  exact mem_FP_pair (mem_FP_pair HU HK.bits_mem_FP) (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP

def flagReader (F : Inputs) (input : List Bool → List Bool) (p : List Bool) :=
  [FlatAffineFullSourceTower.active (F.level (flagQuery F input p))]

theorem flagReader_space {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP) : SpaceFunction (flagReader F input) := by
  have H : (fun w => [FlatAffineFullSourceTower.active w]) ∈ FP :=
    mem_FP_of_eq (FPPred.getBit pairFst_mem_FP (UnaryFn.const 0)).flag_mem_FP (fun w => by
      cases hw : pairFst w with
      | nil => simp [FlatAffineFullSourceTower.active, FlatAffineFullSourceTower.flags, hw]
      | cons b bs => cases b <;> simp [FlatAffineFullSourceTower.active, FlatAffineFullSourceTower.flags, hw])
  exact (hF.level.precompose (flagQuery F input) (flagQuery_FP hF input hi)).postcompose _ H

def maskWord (F : Inputs) (input : List Bool → List Bool) (q : List Bool) :=
  (List.range (arity F (input q))).map (fun j => FlatAffineFullSourceTower.active
    (F.level (FlatAffineFullSourceTower.levelQuery (input q) (F.depth (input q)) j)))

theorem maskWord_space {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP) : SpaceFunction (maskWord F input) := by
  have H := (flagReader_space hF input hi).flatMap_unary ((FlatAffineFullSourceTower.arity_unary hF).comp hi)
  apply H.congr
  funext q
  rw [maskWord, List.map_eq_flatMap]
  simp only [flagReader, flagQuery, pairFst_pair, pairSnd_pair, List.length_replicate]

theorem maskWord_eq (F : Inputs) (input : List Bool → List Bool) (q : List Bool) :
    maskWord F input q = FrozenCoordinatePermutationBits.mask (FlatAffineFullSourceTower.free F (input q) (F.depth (input q))) := by
  apply List.ext_getElem
  · simp only [maskWord, List.length_map, List.length_range, FrozenCoordinatePermutationBits.mask, List.length_ofFn]
  · intro j hj hj'
    simp only [maskWord, List.getElem_map, List.getElem_range, FrozenCoordinatePermutationBits.mask, List.getElem_ofFn]
    simp only [FlatAffineFullSourceTower.free, Finset.mem_filter, Finset.mem_univ, true_and]
    cases FlatAffineFullSourceTower.active (F.level (FlatAffineFullSourceTower.levelQuery (input q) (F.depth (input q)) j)) <;> simp

attribute [local irreducible] FrozenCoordinatePermutationBits.reader maskWord

theorem ordered_evaluator {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP)
    (row : (q : List Bool) → Fin (arity F (input q))) (hr : BinaryFn (fun q => (row q).val)) :
    SpaceFunction (fun q => BinaryNatCode.encode ((FlatAffineExceptionalOrderedRule.order F (input q)) (row q)).val) := by
  have HQ := (maskWord_space hF input hi).pairOutputs (SpaceFunction.ofFP _ hr.bits_mem_FP)
  apply (HQ.postcompose FrozenCoordinatePermutationBits.reader FrozenCoordinatePermutationBits.reader_FP).congr
  funext q
  simp only [Function.comp_apply]
  rw [maskWord_eq]
  exact FrozenCoordinatePermutationBits.reader_mask _ (row q)
end LeanCanny.Encoding.FlatAffineExceptionalSelectorSpace

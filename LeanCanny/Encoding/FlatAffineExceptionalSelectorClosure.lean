/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSelectorSpace
public import LeanCanny.Encoding.FrozenCoordinateMaskEraseFP
/-! # Concrete ordered and coarse affine readers need no permutation oracle -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSelectorSpace
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def coarseMask (F : Inputs) (input : List Bool → List Bool) (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) :=
  FrozenCoordinatePermutationBits.eraseBit (pair (BinaryNatCode.encode (h (input q)).val) (maskWord F input q))

theorem coarseMask_space {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP)
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val)) : SpaceFunction (coarseMask F input h) := by
  have HH : BinaryFn (fun q => (h (input q)).val) := hh.comp hi
  exact ((SpaceFunction.ofFP _ HH.bits_mem_FP).pairOutputs (maskWord_space hF input hi)).postcompose
    FrozenCoordinatePermutationBits.eraseBit FrozenCoordinatePermutationBits.eraseBit_FP

attribute [local irreducible] FrozenCoordinatePermutationBits.reader coarseMask maskWord

theorem coarse_evaluator {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP)
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (row : (q : List Bool) → Fin (arity F (input q))) (hr : BinaryFn (fun q => (row q).val)) :
    SpaceFunction (fun q => BinaryNatCode.encode ((FlatAffineExceptionalCoarseRule.order F h (input q)) (row q)).val) := by
  have HQ := (coarseMask_space hF input hi h hh).pairOutputs (SpaceFunction.ofFP _ hr.bits_mem_FP)
  apply (HQ.postcompose FrozenCoordinatePermutationBits.reader FrozenCoordinatePermutationBits.reader_FP).congr
  funext q
  simp only [Function.comp_apply]
  rw [coarseMask, maskWord_eq, FrozenCoordinatePermutationBits.eraseBit_mask]
  exact FrozenCoordinatePermutationBits.reader_mask _ (row q)

theorem ordered_reference_actual {F : Inputs} (hF : F.Access) (input mod : List Bool → List Bool) (hi : input ∈ FP) (hm : mod ∈ FP)
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (r : (q : List Bool) → Fin (arity F (input q))) (hn : ∀ q, r q ∉ FlatAffineExceptionalOrderedRule.frozen F (input q))
    (row : (q : List Bool) → Fin (arity F (input q))) (hr : BinaryFn (fun q => (row q).val))
    (I : List Bool → ℕ) (hI : BinaryFn I) :
    SpaceFunction (fun q => residueBits (IntegralMixedAffineCoefficients.referenceCoefficient
      ((FlatAffineExceptionalOrderedRule.rule F h (input q) (r q) (hn q)).heights (row q)) (I q) : ZMod (Nat.fromBitsLE (mod q) + 1))) :=
  FlatAffineExceptionalRuleCellsSpace.ordered_reference hF input mod hi hm h hh r hn row (ordered_evaluator hF input hi row hr) I hI

theorem coarse_constant_actual {F : Inputs} (hF : F.Access) (input mod : List Bool → List Bool) (hi : input ∈ FP) (hm : mod ∈ FP)
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (row : (q : List Bool) → Fin (arity F (input q))) (hr : BinaryFn (fun q => (row q).val)) :
    SpaceFunction (fun q => residueBits (IntegralMixedAffineCoefficients.constantCoefficient
      ((FlatAffineExceptionalCoarseRule.rule F h (input q)).heights (row q)) : ZMod (Nat.fromBitsLE (mod q) + 1))) :=
  FlatAffineExceptionalRuleCellsSpace.coarse_constant hF input mod hi hm h hh row (coarse_evaluator hF input hi h hh row hr)

theorem coarse_reference_actual {F : Inputs} (hF : F.Access) (input mod : List Bool → List Bool) (hi : input ∈ FP) (hm : mod ∈ FP)
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (row : (q : List Bool) → Fin (arity F (input q))) (hr : BinaryFn (fun q => (row q).val))
    (I : List Bool → ℕ) (hI : BinaryFn I) :
    SpaceFunction (fun q => residueBits (IntegralMixedAffineCoefficients.referenceCoefficient
      ((FlatAffineExceptionalCoarseRule.rule F h (input q)).heights (row q)) (I q) : ZMod (Nat.fromBitsLE (mod q) + 1))) :=
  FlatAffineExceptionalMixedExpressions.shifted_reference_space hF input mod hi hm h hh _ (coarse_evaluator hF input hi h hh row hr) I hI
end LeanCanny.Encoding.FlatAffineExceptionalSelectorSpace

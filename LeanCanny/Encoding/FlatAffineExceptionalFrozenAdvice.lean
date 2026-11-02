/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalScalarRecipeCorrect
/-! # Original Space preprocessing makes frozen metadata natively readable

Prepared roots contain only the original word and its original level flags.
All readers are total FP on arbitrary supplied roots. Agreement is asserted
only on the actual Space-produced roots; no prefix or matrix is interpreted.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalFrozenAdvice
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FrozenCoordinatePermutationBits.reader FrozenCoordinatePermutationBits.inverseReader FlatAffineExceptionalSelectorSpace.maskWord

noncomputable def prepare (F : Inputs) (u : List Bool) : List Bool :=
  pair u (FlatAffineExceptionalSelectorSpace.maskWord F id u)

theorem prepare_space {F : Inputs} (hF : F.Access) : SpaceFunction (prepare F) :=
  (FlatAffineExceptionalSelectorSpace.maskWord_space hF id id_mem_FP).withInput

theorem original_prepare (F : Inputs) (u : List Bool) : pairFst (prepare F u) = u := pairFst_pair _ _
theorem mask_prepare (F : Inputs) (u : List Bool) : pairSnd (prepare F u) =
    FrozenCoordinatePermutationBits.mask (FlatAffineExceptionalOrderedRule.frozen F u) :=
  (pairSnd_pair _ _).trans (FlatAffineExceptionalSelectorSpace.maskWord_eq F id u)

theorem prepare_length (F : Inputs) (u : List Bool) : (prepare F u).length = 2 * u.length + 2 + arity F u := by
  rw [prepare, pair_length]
  simp only [FlatAffineExceptionalSelectorSpace.maskWord, id_eq, List.length_map, List.length_range]

def countMask (w : List Bool) := ((Finset.range w.length).filter fun j => w[j]?.getD false = true).card

theorem countMask_unary : UnaryFn countMask := by
  have H := UnaryFn.count (UnaryFn.length id_mem_FP) (FPPred.getBit pairFst_mem_FP UnaryFn.index)
  exact H.of_eq (fun w => by simp only [countMask, pairFst_pair, pairSnd_pair, List.length_replicate, id_eq])

theorem countMask_mask {N : ℕ} (s : Finset (Fin N)) : countMask (FrozenCoordinatePermutationBits.mask s) = s.card := by
  unfold countMask
  have HE : (Finset.range (FrozenCoordinatePermutationBits.mask s).length).filter
      (fun j => (FrozenCoordinatePermutationBits.mask s)[j]?.getD false = true) = s.image Fin.val := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, FrozenCoordinatePermutationBits.mask, List.length_ofFn]
    constructor
    · intro hj
      have hm : (⟨j, hj.1⟩ : Fin N) ∈ s := by
        have H := FrozenCoordinatePermutationBits.mask_get s ⟨j, hj.1⟩
        change (List.ofFn fun i => decide (i ∈ s))[j]?.getD false = decide ((⟨j, hj.1⟩ : Fin N) ∈ s) at H
        exact of_decide_eq_true (H.symm.trans hj.2)
      exact Finset.mem_image.mpr ⟨⟨j, hj.1⟩, hm, rfl⟩
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      refine ⟨i.isLt, ?_⟩
      exact (FrozenCoordinatePermutationBits.mask_get s i).trans (decide_eq_true hi)
  rw [HE, Finset.card_image_of_injective s Fin.val_injective]

def offset (prepared : List Bool) := countMask (pairSnd prepared)
theorem offset_unary : UnaryFn offset := countMask_unary.comp pairSnd_mem_FP

theorem offset_prepare (F : Inputs) (u : List Bool) : offset (prepare F u) = (FlatAffineExceptionalOrderedRule.frozen F u).card := by
  rw [offset, mask_prepare, countMask_mask]

def forward (q : List Bool) := FrozenCoordinatePermutationBits.reader (pair (pairSnd (pairFst q)) (pairSnd q))
def inverse (q : List Bool) := FrozenCoordinatePermutationBits.inverseReader (pair (pairSnd (pairFst q)) (pairSnd q))
theorem forward_FP : forward ∈ FP := mem_FP_comp
  (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) FrozenCoordinatePermutationBits.reader_FP
theorem inverse_FP : inverse ∈ FP := mem_FP_comp
  (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) FrozenCoordinatePermutationBits.inverseReader_FP

theorem forward_prepare (F : Inputs) (u : List Bool) (i : Fin (arity F u)) :
    forward (pair (prepare F u) (BinaryNatCode.encode i.val)) =
      BinaryNatCode.encode (FlatAffineExceptionalOrderedRule.order F u i).val := by
  simp only [forward, pairFst_pair, pairSnd_pair]
  rw [mask_prepare]
  exact FrozenCoordinatePermutationBits.reader_mask _ i

theorem inverse_prepare (F : Inputs) (u : List Bool) (i : Fin (arity F u)) :
    inverse (pair (prepare F u) (BinaryNatCode.encode i.val)) =
      BinaryNatCode.encode ((FlatAffineExceptionalOrderedRule.order F u).symm i).val := by
  simp only [inverse, pairFst_pair, pairSnd_pair]
  rw [mask_prepare]
  exact FrozenCoordinatePermutationBits.inverse_reader_mask _ i
end LeanCanny.Encoding.FlatAffineExceptionalFrozenAdvice

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalFrozenAdvice
/-! # Total finite frozen sets decoded from supplied original mask words -/
@[expose] public section
namespace LeanCanny.Encoding.SuppliedFrozenMaskBits
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def selected (N : ℕ) (w : List Bool) : Finset (Fin N) :=
  Finset.univ.filter fun i => w[i.val]?.getD false = true

def normalize (N : ℕ) (w : List Bool) := (List.range N).map fun i => w[i]?.getD false

theorem normalize_mask (N : ℕ) (w : List Bool) : normalize N w = FrozenCoordinatePermutationBits.mask (selected N w) := by
  apply List.ext_getElem
  · simp only [normalize, List.length_map, List.length_range, FrozenCoordinatePermutationBits.mask, List.length_ofFn]
  · intro i hi hj
    simp only [normalize, List.getElem_map, List.getElem_range, FrozenCoordinatePermutationBits.mask, List.getElem_ofFn,
      selected, Finset.mem_filter, Finset.mem_univ, true_and]
    cases w[i]?.getD false <;> rfl

theorem normalize_FP (N : List Bool → ℕ) (hN : UnaryFn N) (w : List Bool → List Bool) (hw : w ∈ FP) :
    (fun q => normalize (N q) (w q)) ∈ FP := by
  have HG := (FPPred.getBit (mem_FP_comp pairFst_mem_FP hw) UnaryFn.index).flag_mem_FP
  apply bitwise_mem_FP hN.mem_FP HG
  intro q i
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]
  cases (w q)[i]?.getD false <;> rfl

theorem selected_mask {N : ℕ} (s : Finset (Fin N)) : selected N (FrozenCoordinatePermutationBits.mask s) = s := by
  ext i
  simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and, FrozenCoordinatePermutationBits.mask_get, decide_eq_true_eq]

def forward (N : ℕ) (w : List Bool) (i : ℕ) :=
  FrozenCoordinatePermutationBits.reader (pair (normalize N w) (BinaryNatCode.encode i))
def inverse (N : ℕ) (w : List Bool) (i : ℕ) :=
  FrozenCoordinatePermutationBits.inverseReader (pair (normalize N w) (BinaryNatCode.encode i))

attribute [local irreducible] FrozenCoordinatePermutationBits.reader FrozenCoordinatePermutationBits.inverseReader

theorem forward_FP (N : List Bool → ℕ) (hN : UnaryFn N) (w : List Bool → List Bool) (hw : w ∈ FP)
    (i : List Bool → ℕ) (hi : BinaryFn i) : (fun q => forward (N q) (w q) (i q)) ∈ FP :=
  mem_FP_comp (mem_FP_pair (normalize_FP N hN w hw) hi.bits_mem_FP) FrozenCoordinatePermutationBits.reader_FP

theorem inverse_FP (N : List Bool → ℕ) (hN : UnaryFn N) (w : List Bool → List Bool) (hw : w ∈ FP)
    (i : List Bool → ℕ) (hi : BinaryFn i) : (fun q => inverse (N q) (w q) (i q)) ∈ FP :=
  mem_FP_comp (mem_FP_pair (normalize_FP N hN w hw) hi.bits_mem_FP) FrozenCoordinatePermutationBits.inverseReader_FP

theorem forward_packet (N : ℕ) (w : List Bool) (i : Fin N) :
    forward N w i.val = BinaryNatCode.encode ((LeanCanny.Geometry.FrozenCoordinateOrdering.permutation (selected N w)) i).val := by
  rw [forward, normalize_mask]
  exact FrozenCoordinatePermutationBits.reader_mask _ i

theorem inverse_packet (N : ℕ) (w : List Bool) (i : Fin N) :
    inverse N w i.val = BinaryNatCode.encode ((LeanCanny.Geometry.FrozenCoordinateOrdering.permutation (selected N w)).symm i).val := by
  rw [inverse, normalize_mask]
  exact FrozenCoordinatePermutationBits.inverse_reader_mask _ i

def offset (N : ℕ) (w : List Bool) := FlatAffineExceptionalFrozenAdvice.countMask (normalize N w)

theorem offset_unary (N : List Bool → ℕ) (hN : UnaryFn N) (w : List Bool → List Bool) (hw : w ∈ FP) :
    UnaryFn (fun q => offset (N q) (w q)) :=
  FlatAffineExceptionalFrozenAdvice.countMask_unary.comp (normalize_FP N hN w hw)

theorem offset_packet (N : ℕ) (w : List Bool) : offset N w = (selected N w).card := by
  rw [offset, normalize_mask, FlatAffineExceptionalFrozenAdvice.countMask_mask]
end LeanCanny.Encoding.SuppliedFrozenMaskBits

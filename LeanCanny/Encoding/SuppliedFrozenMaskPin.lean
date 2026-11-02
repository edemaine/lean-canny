/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SuppliedFrozenMaskFP
/-! # Total frozen masks reserve a height and a distinct free coordinate -/
@[expose] public section
namespace LeanCanny.Encoding.SuppliedFrozenMaskBits
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def pinned {N : ℕ} (w : List Bool) (h r : Fin N) := insert h ((selected N w).erase r)
def pinMask (N : ℕ) (w : List Bool) (h r : ℕ) :=
  (List.range N).map fun i => if i = h then true else if i = r then false else w[i]?.getD false

theorem pinMask_FP (N : List Bool → ℕ) (hN : UnaryFn N) (w : List Bool → List Bool) (hw : w ∈ FP)
    (h r : List Bool → ℕ) (hh : BinaryFn h) (hr : BinaryFn r) :
    (fun q => pinMask (N q) (w q) (h q) (r q)) ∈ FP := by
  have HH := (BinaryFn.ofUnary UnaryFn.index).eq (hh.comp pairFst_mem_FP)
  have HR := (BinaryFn.ofUnary UnaryFn.index).eq (hr.comp pairFst_mem_FP)
  have HB := (FPPred.getBit (mem_FP_comp pairFst_mem_FP hw) UnaryFn.index).flag_mem_FP
  have HG := HH.ite_mem_FP (constFn_mem_FP [true]) (HR.ite_mem_FP (constFn_mem_FP [false]) HB)
  apply bitwise_mem_FP hN.mem_FP HG
  intro q i
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]
  split_ifs <;> rfl

theorem pinMask_mask {N : ℕ} (w : List Bool) (h r : Fin N) :
    pinMask N w h.val r.val = FrozenCoordinatePermutationBits.mask (pinned w h r) := by
  have HP (i : Fin N) : (if i.val = h.val then true else if i.val = r.val then false else w[i.val]?.getD false) = decide (i ∈ pinned w h r) := by
    by_cases hi : i = h
    · subst i
      simp [pinned]
    · by_cases hir : i = r
      · subst i
        simp [pinned, hi, show r.val ≠ h.val from fun he => hi (Fin.ext he)]
      · simp [pinned, selected, hi, hir, show i.val ≠ h.val from fun he => hi (Fin.ext he),
          show i.val ≠ r.val from fun he => hir (Fin.ext he)]
  apply List.ext_getElem
  · simp only [pinMask, List.length_map, List.length_range, FrozenCoordinatePermutationBits.mask, List.length_ofFn]
  · intro j hj hk
    simp only [pinMask, List.getElem_map, List.getElem_range, FrozenCoordinatePermutationBits.mask, List.getElem_ofFn]
    exact HP ⟨j, by simpa only [pinMask, List.length_map, List.length_range] using hj⟩

theorem height_mem {N : ℕ} (w : List Bool) (h r : Fin N) : h ∈ pinned w h r := Finset.mem_insert_self _ _
theorem free_not_mem {N : ℕ} (w : List Bool) (h r : Fin N) (hr : r ≠ h) : r ∉ pinned w h r := by
  simp [pinned, hr]

theorem pinned_original {N : ℕ} (s : Finset (Fin N)) (h r : Fin N) (hh : h ∈ s) (hr : r ∉ s) :
    pinned (FrozenCoordinatePermutationBits.mask s) h r = s := by
  rw [pinned, selected_mask, Finset.erase_eq_of_notMem hr, Finset.insert_eq_of_mem hh]
end LeanCanny.Encoding.SuppliedFrozenMaskBits

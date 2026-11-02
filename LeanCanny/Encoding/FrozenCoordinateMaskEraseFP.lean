/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FrozenCoordinatePermutationCorrect
/-! # Native erasure of one frozen coordinate flag -/
@[expose] public section
namespace LeanCanny.Encoding.FrozenCoordinatePermutationBits
set_option backward.isDefEq.respectTransparency false
open scoped Classical

def eraseBit (q : List Bool) := (List.range (pairSnd q).length).map (fun j =>
  if j = Nat.fromBitsLE (pairFst q) then false else (pairSnd q)[j]?.getD false)
def eraseEntry (p : List Bool) :=
  if (pairSnd p).length = Nat.fromBitsLE (pairFst (pairFst p)) then [false]
  else [(pairSnd (pairFst p))[(pairSnd p).length]?.getD false]

theorem eraseEntry_FP : eraseEntry ∈ FP := by
  have HI := (BinaryFn.ofUnary UnaryFn.index).eq (BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))
  have HB : (fun p => [(pairSnd (pairFst p))[(pairSnd p).length]?.getD false]) ∈ FP :=
    mem_FP_of_eq (FPPred.getBit (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) UnaryFn.index).flag_mem_FP
      (fun p => by cases H : (pairSnd (pairFst p))[(pairSnd p).length]?.getD false <;> simp [Function.comp_apply, H])
  exact HI.ite_mem_FP (constFn_mem_FP [false]) HB

theorem eraseBit_FP : eraseBit ∈ FP := by
  apply bitwise_mem_FP (UnaryFn.length pairSnd_mem_FP).mem_FP eraseEntry_FP
  intro q j
  simp only [eraseEntry, pairFst_pair, pairSnd_pair, List.length_replicate]
  split_ifs <;> rfl

theorem eraseBit_mask {N : ℕ} (s : Finset (Fin N)) (h : Fin N) :
    eraseBit (pair (BinaryNatCode.encode h.val) (mask s)) = mask (s.erase h) := by
  apply List.ext_getElem
  · simp only [eraseBit, pairSnd_pair, List.length_map, List.length_range, mask, List.length_ofFn]
  · intro j hj hj'
    have HJ : j < N := by simpa only [eraseBit, pairSnd_pair, List.length_map, List.length_range, mask, List.length_ofFn] using hj
    have HM := mask_get s (⟨j, HJ⟩ : Fin N)
    simp only [eraseBit, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, List.getElem_map, List.getElem_range]
    rw [HM]
    simp only [mask, List.getElem_ofFn]
    change (if j = h.val then false else decide ((⟨j, HJ⟩ : Fin N) ∈ s)) = decide ((⟨j, HJ⟩ : Fin N) ∈ s.erase h)
    by_cases he : j = h.val
    · rw [ite_eq_left he]
      have HE : (⟨j, HJ⟩ : Fin N) = h := Fin.ext he
      rw [HE]
      simp
    · rw [ite_eq_right he]
      have HE : (⟨j, HJ⟩ : Fin N) ≠ h := fun hz => he (congrArg Fin.val hz)
      apply decide_eq_decide.mpr
      exact ⟨fun hm => Finset.mem_erase.mpr ⟨HE, hm⟩, fun hm => (Finset.mem_erase.mp hm).2⟩
end LeanCanny.Encoding.FrozenCoordinatePermutationBits

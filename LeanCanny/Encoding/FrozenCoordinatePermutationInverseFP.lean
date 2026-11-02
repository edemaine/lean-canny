/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FrozenCoordinatePermutationCorrect
/-! # Native inverse lookup of the exact frozen-first permutation -/
@[expose] public section
namespace LeanCanny.Encoding.FrozenCoordinatePermutationBits
open LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def forwardAtUnary (p : List Bool) := reader (pair (pairFst (pairFst p)) (BinaryNatCode.encode (pairSnd p).length))
def inversePredicate (p : List Bool) : Prop := Nat.fromBitsLE (forwardAtUnary p) = Nat.fromBitsLE (pairSnd (pairFst p))
instance (p : List Bool) : Decidable (inversePredicate p) := inferInstanceAs (Decidable (_ = _))
def inverseIndex (q : List Bool) := (List.range (pairFst q).length).findIdx (fun j => decide (inversePredicate (pair q (List.replicate j true))))
def inverseReader (q : List Bool) := BinaryNatCode.encode (inverseIndex q)

attribute [local irreducible] reader

theorem forwardAtUnary_FP : forwardAtUnary ∈ FP :=
  mem_FP_comp (f := fun p => pair (pairFst (pairFst p)) (BinaryNatCode.encode (pairSnd p).length)) (g := reader)
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP) reader_FP

theorem inversePredicate_FP : FPPred inversePredicate :=
  (BinaryFn.fromBits forwardAtUnary_FP).eq (BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))

theorem inverseIndex_unary : UnaryFn inverseIndex := UnaryFn.find (UnaryFn.length pairFst_mem_FP) inversePredicate_FP

theorem inverseReader_FP : inverseReader ∈ FP := (BinaryFn.ofUnary inverseIndex_unary).bits_mem_FP

theorem inverse_predicate_mask {N : ℕ} (s : Finset (Fin N)) (i : Fin N) (j : ℕ) (hj : j < N) :
    inversePredicate (pair (pair (mask s) (BinaryNatCode.encode i.val)) (List.replicate j true)) ↔
      j = ((FrozenCoordinateOrdering.permutation s).symm i).val := by
  simp only [inversePredicate, forwardAtUnary, pairFst_pair, pairSnd_pair, List.length_replicate]
  rw [reader_mask s ⟨j, hj⟩]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  constructor
  · intro h
    have HE : FrozenCoordinateOrdering.permutation s ⟨j, hj⟩ = i := Fin.ext h
    exact congrArg Fin.val ((FrozenCoordinateOrdering.permutation s).eq_symm_apply.mpr HE)
  · intro h
    have HE : (⟨j, hj⟩ : Fin N) = (FrozenCoordinateOrdering.permutation s).symm i := Fin.ext h
    rw [HE, Equiv.apply_symm_apply]

theorem inverse_reader_mask {N : ℕ} (s : Finset (Fin N)) (i : Fin N) :
    inverseReader (pair (mask s) (BinaryNatCode.encode i.val)) =
      BinaryNatCode.encode ((FrozenCoordinateOrdering.permutation s).symm i).val := by
  unfold inverseReader
  apply congrArg BinaryNatCode.encode
  unfold inverseIndex
  simp only [pairFst_pair, show (mask s).length = N by simp only [mask, List.length_ofFn]]
  apply (List.findIdx_eq (by simpa only [List.length_range] using ((FrozenCoordinateOrdering.permutation s).symm i).isLt)).mpr
  simp only [List.getElem_range]
  constructor
  · exact decide_eq_true ((inverse_predicate_mask s i _ ((FrozenCoordinateOrdering.permutation s).symm i).isLt).mpr rfl)
  · intro j hj
    apply decide_eq_false
    intro hp
    have HE := (inverse_predicate_mask s i j (hj.trans ((FrozenCoordinateOrdering.permutation s).symm i).isLt)).mp hp
    omega
end LeanCanny.Encoding.FrozenCoordinatePermutationBits

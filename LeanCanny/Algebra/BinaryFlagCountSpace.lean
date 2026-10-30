/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ModularSumSpace
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Native exact counts of binary-indexed polynomial-space decisions

The loop count stays binary. Summing indicator residues modulo one more than
the loop count recovers the exact count with a polynomial-length accumulator.
The child's running time is unrestricted.
-/

@[expose] public section
namespace LeanCanny.Algebra.BinaryFlagCountBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def count (test : List Bool → List Bool) (c : List Bool) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun k => test (pair c (BinaryNatCode.encode k)) = [true])).card

theorem count_le (test : List Bool → List Bool) (c : List Bool) (n : ℕ) : count test c n ≤ n :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_range n)

def finish (N : List Bool → ℕ) (z : List Bool) : List Bool :=
  BinaryNat.mod (pair (if pairSnd z = [true] then [true] else [])
    (BinaryNatCode.encode (N (pairFst (pairFst z)) + 1)))

theorem finish_FP {N : List Bool → ℕ} (hN : BinaryFn N) : finish N ∈ FP := by
  have hD : BinaryFn (fun z => N (pairFst (pairFst z))) := hN.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have hM : BinaryFn (fun z => N (pairFst (pairFst z)) + 1) := hD.add (BinaryFn.const 1)
  have hT := (Brackets.stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true])).ite_mem_FP
    (constFn_mem_FP [true]) (constFn_mem_FP [])
  exact mem_FP_comp (mem_FP_pair hT hM.bits_mem_FP) BinaryNat.mod_mem_FP

theorem evaluator {test : List Bool → List Bool} (E : SpaceFunction test)
    {N : List Bool → ℕ} (hN : BinaryFn N) :
    SpaceFunction (fun c => BinaryNatCode.encode (count test c (N c))) := by
  have S := E.withInput.postcompose (finish N) (finish_FP hN)
  have hM := (hN.add (BinaryFn.const 1)).bits_mem_FP
  have hv : (fun c => Nat.fromBitsLE (BinaryNatCode.encode (N c + 1))) = (fun c => N c + 1) := by
    funext c
    exact Nat.fromBitsLE_bits _
  have H := ModularSum.evaluatorWithModulus S (fun c => BinaryNatCode.encode (N c))
    (fun c => BinaryNatCode.encode (N c + 1)) hN.bits_mem_FP hM
    (fun c => N c + 1) hv
    (fun c k => if test (pair c (BinaryNatCode.encode k)) = [true] then (1 : ZMod (N c + 1)) else 0)
    (fun _ => Nat.zero_lt_succ _) (by
      intro c k _
      simp only [Function.comp_apply, finish, pairFst_pair, pairSnd_pair]
      by_cases ht : test (pair c (BinaryNatCode.encode k)) = [true]
      · rw [ite_eq_left ht, ite_eq_left ht]
        simp only [BinaryNat.mod_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, residueBits, ZMod.val_one_eq_one_mod]
        rfl
      · rw [ite_eq_right ht, ite_eq_right ht]
        simp only [BinaryNat.mod_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, residueBits, ZMod.val_zero]
        rfl)
  exact H.congr (funext fun c => by
    rw [show Nat.fromBitsLE (BinaryNatCode.encode (N c)) = N c from Nat.fromBitsLE_bits _]
    have hs : (∑ k ∈ Finset.range (N c), if test (pair c (BinaryNatCode.encode k)) = [true]
        then (1 : ZMod (N c + 1)) else 0) = (count test c (N c) : ZMod (N c + 1)) := by
      simp only [count, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [hs]
    have hl : count test c (N c) < N c + 1 := Nat.lt_succ_of_le (count_le test c (N c))
    let : NeZero (N c + 1) := ⟨Nat.succ_ne_zero _⟩
    simp only [residueBits, ZMod.val_natCast, Nat.mod_eq_of_lt hl]
    )

end LeanCanny.Algebra.BinaryFlagCountBits

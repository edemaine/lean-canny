/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralFrozenPowerSource

/-! # Native actual sums of frozen Fermat height powers

Scan only the original spatial coordinates and omit the free block. Each
remaining power is computed from the original retained-height reader.
The result is an actual old multiplication-matrix entry of frozenPower.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralFrozenPowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def Source.summand (S : Source) (c : List Bool) (i : ℕ) : ℤ := by
  letI := S.ring c
  exact Algebra.leftMulMatrix (S.basis c)
    (if S.offset c ≤ i ∧ i < S.offset c + S.free c then 0 else S.height c i ^ S.allowance c) (S.row c) (S.col c)

noncomputable def Source.sumValue (S : Source) (c : List Bool) : List Bool := by
  letI := S.ring c
  exact residueBits ((Algebra.leftMulMatrix (S.basis c)
    (CoordinateBlockSpecialization.frozenPower (n := S.arity c) (S.height c) (S.offset c) (S.free c) (S.allowance c))
    (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c))

theorem term_packet (S : Source) (c : List Bool) (i : ℕ) :
    termProgram S (pair c (BinaryNatCode.encode i)) = residueBits (S.summand c i : ZMod (S.modulus c)) := by
  generalize hz : pair c (BinaryNatCode.encode i) = p
  have ho : pairFst p = c := by rw [← hz, pairFst_pair]
  have hw : Nat.fromBitsLE (pairSnd p) = i := by rw [← hz, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst c
  let := S.ring (pairFst p)
  have HF : freePosition S p ↔ S.offset (pairFst p) ≤ i ∧ i < S.offset (pairFst p) + S.free (pairFst p) := by
    unfold freePosition
    rw [hw]
  unfold termProgram Source.summand
  by_cases hi : S.offset (pairFst p) ≤ i ∧ i < S.offset (pairFst p) + S.free (pairFst p)
  · rw [ite_eq_left (HF.mpr hi), ite_eq_left hi]
    simp only [map_zero, Matrix.zero_apply, Int.cast_zero, residueBits, ZMod.val_zero,
      BinaryNatCode.encode, Nat.zero_bits]
  · rw [ite_eq_right (fun H => hi (HF.mp H)), ite_eq_right hi, power_value, hw]

theorem sum_summands (S : Source) (c : List Bool) :
    letI := S.ring c
    (∑ i ∈ Finset.range (S.arity c), S.summand c i) =
      Algebra.leftMulMatrix (S.basis c)
        (CoordinateBlockSpecialization.frozenPower (n := S.arity c) (S.height c) (S.offset c) (S.free c) (S.allowance c))
        (S.row c) (S.col c) := by
  let := S.ring c
  rw [CoordinateBlockSpecialization.frozenPower, map_sum, Matrix.sum_apply, Finset.sum_range]
  rfl

theorem sum_value (S : Source) (c : List Bool) :
    residueBits (∑ i ∈ Finset.range (S.arity c), (S.summand c i : ZMod (S.modulus c))) = S.sumValue c := by
  let := S.ring c
  rw [← Int.cast_sum, sum_summands]
  rfl

attribute [local irreducible] Source.sumValue termProgram

theorem sum_evaluator (S : Source) (a : Access S) (EH : SpaceFunction a.height) : SpaceFunction S.sumValue := by
  have E := term_evaluator S a EH
  have HM : (fun c => BinaryNatCode.encode (S.modulus c)) ∈ FP := a.modulus.bits_mem_FP
  have HV : (fun c => Nat.fromBitsLE (BinaryNatCode.encode (S.modulus c))) = S.modulus :=
    funext (fun c => Nat.fromBitsLE_bits _)
  have H := ModularSum.evaluatorWithModulus E (fun c => BinaryNatCode.encode (S.arity c))
    (fun c => BinaryNatCode.encode (S.modulus c)) (bits_mem_FP a.arity) HM S.modulus HV
    (fun c i => (S.summand c i : ZMod (S.modulus c)))
    (fun c => Nat.pos_of_ne_zero (S.modulus_ne_zero c)) (fun c i _ => term_packet S c i)
  refine H.congr (funext fun c => ?_)
  rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact sum_value S c

end LeanCanny.Algebra.IntegralFrozenPowerBits

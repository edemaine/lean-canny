/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMonomialTermEntry

/-! # Original coefficient readers compute the actual cleared-monomial factors -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMonomialTermBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralPowerProductBits (factorWord rowWord colWord)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def packet (c : List Bool) (s r t : ℕ) : List Bool :=
  pair c (pair (BinaryNatCode.encode s) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))

theorem position_packet (c : List Bool) (s r t : ℕ) : position (packet c s r t) = s := by
  simp only [position, packet, factorWord, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem coefficientQuery_packet (c : List Bool) (s r t : ℕ) :
    coefficientQuery (packet c s r t) = pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)) := by
  simp only [coefficientQuery, packet, pairFst_pair, pairSnd_pair]

theorem heightQuery_packet (c : List Bool) (s r t : ℕ) :
    heightQuery (packet c s r t) =
      pair c (pair (BinaryNatCode.encode (s - 2)) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))) := by
  unfold heightQuery index
  rw [position_packet]
  simp only [packet, pairFst_pair, pairSnd_pair]

theorem sameIndex_packet (c : List Bool) (s : ℕ) {M : ℕ} (r t : Fin M) :
    sameIndex (packet c s r.val t.val) ↔ r = t := by
  simp only [sameIndex, packet, rowWord, colWord, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Fin.ext_iff]

theorem scalar_packet (S : Source) (a : Access S) (c : List Bool) (s : ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    scalarProgram a (packet c s r.val t.val) =
      residueBits ((Algebra.leftMulMatrix (S.basis c) (S.denominator c : S.carrier c) r t : ℤ) : ZMod (S.modulus c)) := by
  let := S.ring c
  rw [scalarProgram, map_intCast, Matrix.intCast_apply]
  simp only [Int.cast_id]
  by_cases h : r = t
  · rw [ite_eq_left ((sameIndex_packet c s r t).mpr h), ite_eq_left h]
    simpa only [packet, pairFst_pair] using a.denominator_eq c
  · rw [ite_eq_right (fun H => h ((sameIndex_packet c s r t).mp H)), ite_eq_right h]
    simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

theorem unit_packet (S : Source) (c : List Bool) (s : ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    unitProgram S (packet c s r.val t.val) =
      residueBits ((Algebra.leftMulMatrix (S.basis c) 1 r t : ℤ) : ZMod (S.modulus c)) := by
  let := S.ring c
  let : NeZero (S.modulus c) := ⟨S.modulus_ne_zero c⟩
  rw [unitProgram, map_one, Matrix.one_apply]
  by_cases h : r = t
  · rw [ite_eq_left ((sameIndex_packet c s r t).mpr h), ite_eq_left h]
    simpa only [packet, pairFst_pair, Int.cast_one] using ArithmeticBits.one_residueBits (S.modulus c)
  · rw [ite_eq_right (fun H => h ((sameIndex_packet c s r t).mp H)), ite_eq_right h]
    simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

theorem entry_correct (S : Source) (a : Access S) (c : List Bool) (s : ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    entryProgram S a (packet c s r.val t.val) =
      residueBits ((Algebra.leftMulMatrix (S.basis c) (factor S c s) r t : ℤ) : ZMod (S.modulus c)) := by
  let := S.ring c
  have HV : valid S (packet c s r.val t.val) ↔ s - 2 < S.arity c := by
    unfold valid index
    rw [position_packet]
    simp only [packet, pairFst_pair]
  have HF : freeIndex S (packet c s r.val t.val) ↔ isFree S c (s - 2) := by
    unfold freeIndex index
    rw [position_packet]
    simp only [packet, pairFst_pair]
  rw [entryProgram, position_packet]
  by_cases h0 : s = 0
  · rw [ite_eq_left h0, coefficientQuery_packet, a.coefficient_eq, factor, ite_eq_left h0]
  · rw [ite_eq_right h0]
    by_cases h1 : s = 1
    · rw [ite_eq_left h1, scalar_packet, factor, ite_eq_right h0, ite_eq_left h1]
    · rw [ite_eq_right h1]
      by_cases hv : s - 2 < S.arity c
      · rw [ite_eq_left (HV.mpr hv)]
        by_cases hf : isFree S c (s - 2)
        · rw [ite_eq_left (HF.mpr hf), scalar_packet, factor, ite_eq_right h0, ite_eq_right h1,
            ite_eq_left hv, ite_eq_left hf]
        · rw [ite_eq_right (fun H => hf (HF.mp H)), heightQuery_packet, a.height_eq,
            factor, ite_eq_right h0, ite_eq_right h1, ite_eq_left hv, ite_eq_right hf]
      · rw [ite_eq_right (fun H => hv (HV.mp H)), unit_packet, factor,
          ite_eq_right h0, ite_eq_right h1, ite_eq_right hv]

end LeanCanny.Algebra.IntegralMonomialTermBits

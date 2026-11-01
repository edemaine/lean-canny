/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayIntegralEntryRequest

/-! # Literal shifted-coefficient packets and their original grid bound -/

@[expose] public section
namespace LeanCanny.Algebra.MacaulayIntegralQueryBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial MacaulayFullBoxBits

def differenceRank (L : Layout) (q : List Bool) (a b r t : ℕ) : ℕ :=
  Nat.fromBitsLE (differenceWord L (packet q (a / count (L.arity q) (L.width q))
    (a % count (L.arity q) (L.width q)) b r t))

theorem query_packet (L : Layout) (q : List Bool) (a b r t : ℕ) :
    MacaulayIntegralEntryRequest.query L (entryPacket q a b r t) =
      entryPacket q (a / count (L.arity q) (L.width q)) (differenceRank L q a b r t) r t := by
  simp only [MacaulayIntegralEntryRequest.query, rawSourceInput, ctx_entryPacket, idx_entryPacket,
    shift_entryPacket, uv_entryPacket, columnsCode_eq, BinaryNat.divMod_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, pairFst_pair, pairSnd_pair]
  simp only [sourceInput, ctx, idx, parameters, pairFst_pair, pairSnd_pair]
  rw [BinaryNat.normalize_eq_bits]
  rfl

theorem differenceRank_lt (L : Layout) (q : List Bool) (a b r t : ℕ) :
    differenceRank L q a b r t < count (L.arity q) (L.width q) := by
  have H := Nat.fromBitsLE_lt_pow_length (differenceWord L
    (packet q (a / count (L.arity q) (L.width q)) (a % count (L.arity q) (L.width q)) b r t))
  simp only [differenceWord, ctx_packet, FixedWidthNatVector.length_encode] at H
  rw [count, ← pow_mul]
  simpa only [differenceRank, differenceWord, ctx_packet, Nat.mul_comm] using H

theorem sourceRow_lt (L : Layout) (q : List Bool) (a b r t : ℕ)
    (h : MacaulayIntegralEntryRequest.request L (entryPacket q a b r t)) :
    a / count (L.arity q) (L.width q) < L.arity q := by
  have HS := h.2.1
  have HA : a < L.arity q * count (L.arity q) (L.width q) := by
    simpa only [isSource, idx_entryPacket, ctx_entryPacket, sourceCut_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits] using HS
  exact (Nat.div_lt_iff_lt_mul (pow_pos (Nat.two_pow_pos _) _)).mpr HA

end LeanCanny.Algebra.MacaulayIntegralQueryBounds

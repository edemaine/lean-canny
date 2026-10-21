/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SumBitController

/-!
# Correctness of the streamed sum-bit controller

Every abstract step adds one requested bit or advances to the next column by
halving the accumulated total. The invariant gives the exact encoded state at
every step, including row boundaries and the empty family of summands.
-/

@[expose] public section

namespace LeanCanny.Computation.SumBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Algebra
open scoped BigOperators

@[simp] theorem context_packet (c : List Bool) (t v : ℕ) : pairFst (packet c t v) = c := by simp [packet]
@[simp] theorem counter_packet (c : List Bool) (t v : ℕ) : counter (packet c t v) = BinaryNatCode.encode t := by
  simp [packet, counter]
@[simp] theorem accumulator_packet (c : List Bool) (t v : ℕ) :
    accumulator (packet c t v) = BinaryNatCode.encode v := by simp [packet, accumulator]

theorem coordinate_packet (count : List Bool → List Bool) (c : List Bool) (N t v : ℕ)
    (hc : Nat.fromBitsLE (count c) = N) :
    coordinate count (packet c t v) =
      pair (BinaryNatCode.encode (t / (N + 1))) (BinaryNatCode.encode (t % (N + 1))) := by
  simp only [coordinate, counter_packet, context_packet, width, BinaryNat.divMod_pair,
    BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, hc]

theorem query_packet (count : List Bool → List Bool) (c : List Bool) (N t v : ℕ)
    (hc : Nat.fromBitsLE (count c) = N) :
    query count (packet c t v) =
      pair c (pair (BinaryNatCode.encode (t % (N + 1))) (BinaryNatCode.encode (t / (N + 1)))) := by
  simp only [query, position, column, coordinate_packet count c N t v hc, context_packet,
    pairFst_pair, pairSnd_pair]

theorem request_packet (count : List Bool → List Bool) (c : List Bool) (N t v : ℕ)
    (hc : Nat.fromBitsLE (count c) = N) :
    request count (packet c t v) = decide (t % (N + 1) < N) := by
  simp only [request, position, coordinate_packet count c N t v hc, context_packet,
    pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, hc]

theorem limit_code (count index : List Bool → List Bool) (c : List Bool) :
    limit count index c = BinaryNatCode.encode
      (Nat.fromBitsLE (index c) * (Nat.fromBitsLE (count c) + 1) + Nat.fromBitsLE (count c)) := by
  simp only [limit, width, BinaryNat.add_eq_bits, BinaryNat.mul_eq_bits, BinaryNat.succ_eq_bits,
    pairFst_pair, pairSnd_pair, Nat.fromBitsLE_bits, BinaryNatCode.encode]

theorem halted_packet (count index : List Bool → List Bool) (c : List Bool) (t v : ℕ) :
    halted count index (packet c t v) = decide
      (Nat.fromBitsLE (index c) * (Nat.fromBitsLE (count c) + 1) + Nat.fromBitsLE (count c) ≤ t) := by
  simp only [halted, context_packet, counter_packet, limit_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem ordinary_packet (c : List Bool) (t v : ℕ) : ordinary (packet c t v) = packet c (t + 1) (v / 2) := by
  rw [ordinary, context_packet, counter_packet, accumulator_packet]
  simp only [BinaryNat.succ_eq_bits, BinaryNat.div_eq_bits, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, show Nat.fromBitsLE [false, true] = 2 from rfl, packet]

theorem resume_packet
    (c : List Bool) (t v : ℕ) (u : List Bool) :
    resume (pair (packet c t v) u) =
      packet c (t + 1) (v + if u[0]?.getD false then 1 else 0) := by
  simp only [resume, response, pairFst_pair, pairSnd_pair, context_packet, counter_packet, accumulator_packet]
  cases u[0]?.getD false <;>
    simp only [Bool.false_eq_true, ↓reduceIte, BinaryNat.succ_eq_bits, BinaryNat.add_eq_bits,
      pairFst_pair, pairSnd_pair, packet, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      show Nat.fromBitsLE [] = 0 from rfl, show Nat.fromBitsLE [true] = 1 from rfl, Nat.add_zero]

theorem output_packet (c : List Bool) (t v : ℕ) : output (packet c t v) = (v % 2).bits := by
  simp only [output, accumulator_packet, BinaryNat.mod_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    show Nat.fromBitsLE [false, true] = 2 from rfl]

theorem step_packet (f : List Bool → List Bool) (count : List Bool → List Bool)
    (c : List Bool) (N : ℕ) (a : ℕ → ℕ) (hc : Nat.fromBitsLE (count c) = N)
    (hbits : ∀ i k, i < N → (f (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false =
      (a i).testBit k) (t : ℕ) :
    step f count
      (packet c t (BinarySum.carryValue N a t)) = packet c (t + 1) (BinarySum.carryValue N a (t + 1)) := by
  by_cases hi : t % (N + 1) < N
  · simp only [step, request_packet count c N t _ hc,
      hi, decide_true, ↓reduceIte]
    rw [resume_packet, query_packet count c N t _ hc, hbits _ _ hi,
      ← BinarySum.bit_eq, ← BinarySum.carryValue_succ_bit N a t hi]
  · simp only [step, request_packet count c N t _ hc,
      hi, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [ordinary_packet, ← BinarySum.carryValue_succ_carry N a t hi]

theorem iterate_packet (f : List Bool → List Bool) (count : List Bool → List Bool)
    (c : List Bool) (N : ℕ) (a : ℕ → ℕ) (hc : Nat.fromBitsLE (count c) = N)
    (hbits : ∀ i k, i < N → (f (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false =
      (a i).testBit k) (t : ℕ) :
    (step f count)^[t] (init c) =
      packet c t (BinarySum.carryValue N a t) := by
  induction t with
  | zero => simp only [Function.iterate_zero_apply, BinarySum.carryValue_zero]; rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, step_packet f count c N a hc hbits]

theorem output_end (f : List Bool → List Bool) (count : List Bool → List Bool)
    (c : List Bool) (N K : ℕ) (a : ℕ → ℕ) (hc : Nat.fromBitsLE (count c) = N)
    (hbits : ∀ i k, i < N → (f (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false =
      (a i).testBit k) :
    output ((step f count)^[K * (N + 1) + N] (init c)) =
      if (∑ i ∈ Finset.range N, a i).testBit K then [true] else [] := by
  rw [iterate_packet f count c N a hc hbits, output_packet, BinarySum.carryValue_end,
    BinarySum.sum_testBit, BinarySum.partialColumn]
  have hl := Nat.mod_lt (BinarySum.carry N a K + BinarySum.column N a K) (by decide : 0 < 2)
  have hd : (BinarySum.carry N a K + BinarySum.column N a K) % 2 = 0 ∨
      (BinarySum.carry N a K + BinarySum.column N a K) % 2 = 1 := by omega
  rcases hd with h | h <;> simp [h]

end LeanCanny.Computation.SumBits

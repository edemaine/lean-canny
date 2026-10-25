/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.NumericPayloadFP
public import LeanCanny.Computation.PolyTimeBinaryNat
public import LeanCanny.Computation.PolyTimeRange

/-! # Binary natural and negative-natural literal writers

The serialized integer magnitude remains binary. In particular, direction
coordinates never become unary counters when written as circuit constants.
-/

@[expose] public section
namespace LeanCanny.ETR
open LeanCanny.Encoding.Brackets Turing.MultiTapeTM

theorem Codec.BitPayload.body_mem_FP : Codec.BitPayload.body ∈ FP := by
  have hb : ComputableTidilyInPolyTime (fun b : Bool => (Codec.bit b).toBits) encBool encBits :=
    ComputableTidilyInPolyTime.of_finite _
  exact ComputableTidilyInPolyTime.bitsFlatten
    ((ComputableTidilyInPolyTime.map hb).comp ComputableTidilyInPolyTime.bitsToList)

theorem Codec.natural_toBits_mem_FP {n : List Bool → ℕ} (hn : BinaryFn n) :
    (fun c => (Codec.natural (n c)).toBits) ∈ FP := by
  have h := mem_FP_comp (mem_FP_comp hn.bits_mem_FP Codec.BitPayload.body_mem_FP) wrap_mem_FP
  exact mem_FP_of_eq h (fun c => (Codec.natural_toBits (n c)).symm)

theorem Term.negNat_toBits_mem_FP {n : List Bool → ℕ} (hn : BinaryFn n) :
    (fun c => (Term.const (-(n c : ℤ))).toData.toBits) ∈ FP := by
  have he := BinaryFn.eq hn (BinaryFn.const 0)
  have hneg := Codec.taggedOne_mem_FP 0 (Codec.taggedOne_mem_FP 1
    (Codec.natural_toBits_mem_FP (hn.sub (BinaryFn.const 1))))
  have h := he.ite_mem_FP (constFn_mem_FP (Term.const 0).toData.toBits) hneg
  apply mem_FP_of_eq h
  intro c
  by_cases hc : n c = 0
  · simp only [hc, ite_true, Nat.cast_zero, neg_zero]
  · have hz : -(n c : ℤ) = Int.negSucc (n c - 1) := by omega
    simp only [ite_eq_right hc, hz, Codec.taggedOne_toBits, Term.toData, Codec.integer]

theorem Term.nat_toBits_mem_FP {n : List Bool → ℕ} (hn : BinaryFn n) :
    (fun c => (Term.const (n c : ℤ)).toData.toBits) ∈ FP := by
  have h := Codec.taggedOne_mem_FP 0 (Codec.taggedOne_mem_FP 0 (Codec.natural_toBits_mem_FP hn))
  exact mem_FP_of_eq h (fun c => by simp only [Codec.taggedOne_toBits, Term.toData, Codec.integer])

end LeanCanny.ETR

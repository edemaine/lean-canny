/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CanonicalNodeContext
public import LeanCanny.Computation.PolyTimeArithmetic

/-! # Total FP queries along a finite-tree leaf path

An input pairs the original source with a leaf index. A stage pairs this
input with a binary counter. Capping the counter and leaf index keeps every
query polynomial in size, including malformed inputs and count zero.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteLeafPathContext
open LeanCanny.Encoding

def leafContext (u : List Bool) : List Bool := BalancedParameterContext.packet (pairFst u) 0 (Nat.fromBitsLE (pairSnd u))
def leafIndex (count : List Bool → ℕ) (u : List Bool) : ℕ := CanonicalNodeContext.index count (leafContext u)
def depth (count : List Bool → ℕ) (u : List Bool) : ℕ := (count (pairFst u)).size
def stage (count : List Bool → ℕ) (p : List Bool) : ℕ := min (Nat.fromBitsLE (pairSnd p)) (depth count (pairFst p))
def position (count : List Bool → ℕ) (p : List Bool) : ℕ := leafIndex count (pairFst p) / 2 ^ stage count p
def right (count : List Bool → ℕ) (p : List Bool) : Prop := position count p % 2 = 1
def parent (count : List Bool → ℕ) (p : List Bool) : List Bool :=
  BalancedParameterContext.packet (pairFst (pairFst p)) (stage count p + 1) (position count p / 2)

theorem leafContext_FP : leafContext ∈ FP :=
  BalancedParameterContext.packet_FP pairFst_mem_FP (UnaryFn.const 0) (BinaryFn.fromBits pairSnd_mem_FP)

theorem leafIndex_unary {count : List Bool → ℕ} (hn : UnaryFn count) : UnaryFn (leafIndex count) :=
  (CanonicalNodeContext.index_unary hn).comp leafContext_FP

theorem depth_unary {count : List Bool → ℕ} (hn : UnaryFn count) : UnaryFn (depth count) := (hn.comp pairFst_mem_FP).size

theorem stage_unary {count : List Bool → ℕ} (hn : UnaryFn count) : UnaryFn (stage count) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP ((depth_unary hn).comp pairFst_mem_FP)

theorem leafIndex_lt (count : List Bool → ℕ) (u : List Bool) : leafIndex count u < 2 ^ depth count u := by
  have h := CanonicalNodeContext.index_lt count (leafContext u)
  simpa only [leafIndex, CanonicalNodeContext.width, CanonicalNodeContext.height,
    BalancedCanonicalDegrees.boundedHeight, leafContext, BalancedParameterContext.original_packet,
    BalancedParameterContext.height_packet, Nat.zero_min, Nat.sub_zero, depth] using h

theorem leafIndex_packet (count : List Bool → ℕ) (c : List Bool) (j : ℕ) (hj : j < 2 ^ (count c).size) :
    leafIndex count (pair c (BinaryNatCode.encode j)) = j := by
  simp only [leafIndex, leafContext, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact CanonicalNodeContext.index_packet count c 0 j (Nat.zero_le _) (by simpa only [Nat.sub_zero] using hj)

theorem stage_packet (count : List Bool → ℕ) (u : List Bool) (s : ℕ) (hs : s ≤ depth count u) :
    stage count (pair u (BinaryNatCode.encode s)) = s := by
  simp only [stage, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, min_eq_left hs]

theorem power_unary {count : List Bool → ℕ} (hn : UnaryFn count) : UnaryFn (fun p => 2 ^ stage count p) := by
  have hp : BinaryFn (fun p => 2 ^ stage count p) := (BinaryFn.const 2).powUnary (stage_unary hn)
  have nc := hn.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have hcap := (UnaryFn.const 2).mul (nc.add (UnaryFn.const 1))
  have H := UnaryFn.fromBitsLE_of_le hp.bits_mem_FP hcap (fun p => by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have hs : stage count p ≤ (count (pairFst (pairFst p))).size := min_le_right _ _
    exact (Nat.pow_le_pow_right (by decide) hs).trans (FiniteAnnihilatorTree.width_bound _))
  exact H.of_eq (fun p => Nat.fromBitsLE_bits _)

theorem position_unary {count : List Bool → ℕ} (hn : UnaryFn count) : UnaryFn (position count) :=
  ((leafIndex_unary hn).comp pairFst_mem_FP).div (power_unary hn)

theorem right_fppred {count : List Bool → ℕ} (hn : UnaryFn count) : FPPred (right count) := by
  have hm := bits_mem_FP ((position_unary hn).mod (UnaryFn.const 2))
  simpa only [Nat.fromBitsLE_bits] using BinaryNat.eq_const_fppred hm 1

theorem parent_FP {count : List Bool → ℕ} (hn : UnaryFn count) : parent count ∈ FP :=
  BalancedParameterContext.packet_FP (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    ((stage_unary hn).add (UnaryFn.const 1))
    (BinaryFn.of_bits (bits_mem_FP ((position_unary hn).div (UnaryFn.const 2))))

end LeanCanny.Algebra.FiniteLeafPathContext

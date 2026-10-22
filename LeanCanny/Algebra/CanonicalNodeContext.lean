/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedCanonicalDegrees

/-! # Total FP contexts for valid canonical finite-tree nodes

Heights are capped at the finite count's binary size. Indices are capped at
the layer width minus one, including for count zero. Thus every word names
a genuine node of the padded finite tree.
-/

@[expose] public section

namespace LeanCanny.Algebra.CanonicalNodeContext
open LeanCanny.Encoding
open BalancedParameterContext (original)

def height (count : List Bool → ℕ) (p : List Bool) : ℕ := BalancedCanonicalDegrees.boundedHeight count p
def width (count : List Bool → ℕ) (p : List Bool) : ℕ := 2 ^ ((count (original p)).size - height count p)
def index (count : List Bool → ℕ) (p : List Bool) : ℕ := min (BalancedParameterContext.index p) (width count p - 1)
def packet (count : List Bool → ℕ) (p : List Bool) : List Bool := BalancedParameterContext.packet (original p) (height count p) (index count p)

theorem height_le (count : List Bool → ℕ) (p : List Bool) : height count p ≤ (count (original p)).size := min_le_right _ _

theorem width_pos (count : List Bool → ℕ) (p : List Bool) : 0 < width count p := Nat.two_pow_pos _

theorem index_lt (count : List Bool → ℕ) (p : List Bool) : index count p < width count p := by
  have h := min_le_right (BalancedParameterContext.index p) (width count p - 1)
  have hw := width_pos count p
  dsimp only [index]
  omega

theorem height_unary {count : List Bool → ℕ} (hn : UnaryFn count) : UnaryFn (height count) :=
  BalancedCanonicalDegrees.boundedHeight_unary hn

theorem width_unary {count : List Bool → ℕ} (hn : UnaryFn count) : UnaryFn (width count) := by
  have hs : UnaryFn (fun p => (count (original p)).size) := (hn.comp BalancedParameterContext.original_FP).size
  have hw : BinaryFn (width count) := (BinaryFn.const 2).powUnary (hs.sub (height_unary hn))
  have hcap := (UnaryFn.const 2).mul ((hn.comp BalancedParameterContext.original_FP).add (UnaryFn.const 1))
  have h := UnaryFn.fromBitsLE_of_le hw.bits_mem_FP hcap (fun p => by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)).trans (FiniteAnnihilatorTree.width_bound _))
  exact h.of_eq (fun p => Nat.fromBitsLE_bits _)

theorem index_unary {count : List Bool → ℕ} (hn : UnaryFn count) : UnaryFn (index count) :=
  UnaryFn.fromBitsLE_min BalancedParameterContext.indexWord_FP ((width_unary hn).sub (UnaryFn.const 1))

theorem packet_FP {count : List Bool → ℕ} (hn : UnaryFn count) : packet count ∈ FP :=
  BalancedParameterContext.packet_FP BalancedParameterContext.original_FP (height_unary hn)
    (BinaryFn.of_bits (bits_mem_FP (index_unary hn)))

theorem height_packet (count : List Bool → ℕ) (c : List Bool) (h i : ℕ) (hh : h ≤ (count c).size) :
    height count (BalancedParameterContext.packet c h i) = h := by
  simp only [height, BalancedCanonicalDegrees.boundedHeight, BalancedParameterContext.original_packet,
    BalancedParameterContext.height_packet, min_eq_left hh]

theorem index_packet (count : List Bool → ℕ) (c : List Bool) (h i : ℕ)
    (hh : h ≤ (count c).size) (hi : i < 2 ^ ((count c).size - h)) :
    index count (BalancedParameterContext.packet c h i) = i := by
  simp only [index, width, BalancedParameterContext.original_packet, BalancedParameterContext.index_packet,
    height_packet count c h i hh]
  exact min_eq_left (by omega)

end LeanCanny.Algebra.CanonicalNodeContext

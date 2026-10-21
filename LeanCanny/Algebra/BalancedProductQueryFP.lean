/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedProductEncoding
public import LeanCanny.Encoding.BinaryDivFP
public import LeanCanny.Tactic.PolyTime

/-!
# Certified binary query transformations for balanced product bits

Child heights, node addresses, and bit indices are computed directly on binary
words. FP division decodes scan coordinates. The initial height is the length
of the factor-count word, so its magnitude is never expanded to unary.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedProduct.QueryBits

open LeanCanny.Encoding

def height (q : List Bool) : List Bool := pairFst q
def node (q : List Bool) : List Bool := pairFst (pairSnd q)
def index (q : List Bool) : List Bool := pairSnd (pairSnd q)
def build (h n k : List Bool) : List Bool := pair h (pair n k)
def width (q : List Bool) : List Bool := BinaryNat.add (pair (index q) (BinaryNatCode.encode 2))
def coordinate (p : List Bool) : List Bool := BinaryNat.divMod (pair (pairSnd p) (width (pairFst p)))
def doubleNode (q : List Bool) : List Bool := BinaryNat.add (pair (node q) (node q))

def childLeft (p : List Bool) : List Bool :=
  build (BinaryNat.pred (height (pairFst p))) (doubleNode (pairFst p)) (pairSnd (coordinate p))
def childRight (p : List Bool) : List Bool :=
  build (BinaryNat.pred (height (pairFst p))) (BinaryNat.succ (doubleNode (pairFst p)))
    (BinaryNat.sub (pair (pairFst (coordinate p)) (pairSnd (coordinate p))))

def initial (count index : List Bool → List Bool) (c : List Bool) : List Bool :=
  build (BinaryNatCode.encode (count c).length) [] (BinaryNat.normalize (index c))

theorem height_mem_FP : height ∈ FP := pairFst_mem_FP
theorem node_mem_FP : node ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem index_mem_FP : index ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

theorem build_mem_FP {h n k : List Bool → List Bool} (hh : h ∈ FP) (hn : n ∈ FP) (hk : k ∈ FP) :
    (fun c => build (h c) (n c) (k c)) ∈ FP := mem_FP_pair hh (mem_FP_pair hn hk)

theorem width_mem_FP : width ∈ FP := by
  have he := mem_FP_comp (mem_FP_pair index_mem_FP (constFn_mem_FP (BinaryNatCode.encode 2))) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := width) he ?_
  intro q
  simp only [Function.comp_apply, width]

theorem coordinate_mem_FP : coordinate ∈ FP := by
  have hw := mem_FP_comp pairFst_mem_FP width_mem_FP
  have he := mem_FP_comp (mem_FP_pair pairSnd_mem_FP hw) BinaryNat.divMod_mem_FP
  refine mem_FP_of_eq (g := coordinate) he ?_
  intro p
  simp only [Function.comp_apply, coordinate]

theorem doubleNode_mem_FP : doubleNode ∈ FP := by
  have he := mem_FP_comp (mem_FP_pair node_mem_FP node_mem_FP) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := doubleNode) he ?_
  intro q
  simp only [Function.comp_apply, doubleNode]

theorem childLeft_mem_FP : childLeft ∈ FP := by
  have hh := mem_FP_comp (mem_FP_comp pairFst_mem_FP height_mem_FP) BinaryNat.pred_mem_FP
  have hn := mem_FP_comp pairFst_mem_FP doubleNode_mem_FP
  have hk := mem_FP_comp coordinate_mem_FP pairSnd_mem_FP
  have he := build_mem_FP hh hn hk
  refine mem_FP_of_eq (g := childLeft) he ?_
  intro p
  simp only [Function.comp_apply, childLeft]

theorem childRight_mem_FP : childRight ∈ FP := by
  have hh := mem_FP_comp (mem_FP_comp pairFst_mem_FP height_mem_FP) BinaryNat.pred_mem_FP
  have hn := mem_FP_comp (mem_FP_comp pairFst_mem_FP doubleNode_mem_FP) BinaryNat.succ_mem_FP
  have hj := mem_FP_comp coordinate_mem_FP pairFst_mem_FP
  have hi := mem_FP_comp coordinate_mem_FP pairSnd_mem_FP
  have hk := mem_FP_comp (mem_FP_pair hj hi) BinaryNat.sub_mem_FP
  have he := build_mem_FP hh hn hk
  refine mem_FP_of_eq (g := childRight) he ?_
  intro p
  simp only [Function.comp_apply, childRight]

theorem initial_mem_FP {count index : List Bool → List Bool} (hc : count ∈ FP) (hi : index ∈ FP) : initial count index ∈ FP := by
  have hh := bits_mem_FP (UnaryFn.length hc)
  have hk := mem_FP_comp hi BinaryNat.normalize_mem_FP
  have he := build_mem_FP hh (constFn_mem_FP []) hk
  refine mem_FP_of_eq (g := initial count index) he ?_
  intro c
  simp only [Function.comp_apply, initial, BinaryNatCode.encode]

theorem width_queryBits (q : Query) : width (queryBits q) = BinaryNatCode.encode (BalancedProduct.width q.index) := by
  simp only [width, index, queryBits, pairSnd_pair, BinaryNat.add_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, BalancedProduct.width]

theorem coordinate_packet (q : Query) (t : ℕ) : coordinate (pair (queryBits q) (BinaryNatCode.encode t)) =
    pair (BinaryNatCode.encode (column q.index t)) (BinaryNatCode.encode (position q.index t)) := by
  simp only [coordinate, pairFst_pair, pairSnd_pair, width_queryBits, BinaryNat.divMod_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, column, position]

theorem doubleNode_queryBits (q : Query) : doubleNode (queryBits q) = BinaryNatCode.encode (2 * q.node) := by
  simp only [doubleNode, node, queryBits, pairFst_pair, pairSnd_pair, BinaryNat.add_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, two_mul]

theorem childLeft_queryBits (q : Query) (t : ℕ) :
    childLeft (pair (queryBits q) (BinaryNatCode.encode t)) = queryBits (q.left t) := by
  rw [childLeft, pairFst_pair, doubleNode_queryBits, coordinate_packet]
  simp only [height, queryBits, pairFst_pair, pairSnd_pair, BinaryNat.pred_eq_bits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Query.left, build]

theorem childRight_queryBits (q : Query) (t : ℕ) :
    childRight (pair (queryBits q) (BinaryNatCode.encode t)) = queryBits (q.right t) := by
  rw [childRight, pairFst_pair, doubleNode_queryBits, coordinate_packet]
  simp only [height, queryBits, pairFst_pair, pairSnd_pair, BinaryNat.pred_eq_bits, BinaryNat.succ_eq_bits,
    BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Query.right, build]

theorem initial_queryBits (count index : List Bool → List Bool) (c : List Bool) :
    initial count index c = queryBits ⟨(count c).length, 0, Nat.fromBitsLE (index c)⟩ := by
  simp only [initial, queryBits, build, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]
  rfl

end LeanCanny.Algebra.BalancedProduct.QueryBits

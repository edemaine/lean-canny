/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteAnnihilatorTree
public import LeanCanny.Encoding.BinaryNatFP
public import LeanCanny.Computation.PolyTimeArithmetic
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Concrete contexts for balanced primitive-parameter nodes

A context stores the original input, a unary remaining height, and a binary
node index. Descending drops one height bit and appends the branch bit at the
low end of the binary index. Normalization keeps indices canonical. The
decoded height decreases on every nonleaf step, including malformed inputs;
on paired contexts the complete node word strictly shrinks.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedParameterContext
open LeanCanny.Encoding

def original : List Bool → List Bool := pairFst
def heightWord (p : List Bool) : List Bool := pairFst (pairSnd p)
def indexWord (p : List Bool) : List Bool := pairSnd (pairSnd p)
def height (p : List Bool) : ℕ := (heightWord p).length
def index (p : List Bool) : ℕ := Nat.fromBitsLE (indexWord p)

def packet (c : List Bool) (h i : ℕ) : List Bool :=
  pair c (pair (List.replicate h true) (BinaryNatCode.encode i))

def child (right : Bool) (p : List Bool) : List Bool :=
  pair (original p) (pair ((heightWord p).drop 1) (BinaryNat.normalize (right :: indexWord p)))

attribute [local irreducible] BinaryNat.normalize

theorem original_FP : original ∈ FP := pairFst_mem_FP
theorem heightWord_FP : heightWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem indexWord_FP : indexWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem height_unary : UnaryFn height := UnaryFn.length heightWord_FP

theorem packet_FP {c : List Bool → List Bool} {h i : List Bool → ℕ}
    (hc : c ∈ FP) (hh : UnaryFn h) (hi : BinaryFn i) :
    (fun p => packet (c p) (h p) (i p)) ∈ FP :=
  mem_FP_pair hc (mem_FP_pair (hh.replicate_mem_FP true) hi.bits_mem_FP)

theorem root_FP {count : List Bool → ℕ} (hn : BinaryFn count) :
    (fun c => packet c (count c).size 0) ∈ FP := by
  have hh : UnaryFn (fun c => (count c).size) :=
    (UnaryFn.length hn.bits_mem_FP).of_eq (fun c => Nat.size_eq_bits_len (count c))
  exact packet_FP id_mem_FP hh (BinaryFn.const 0)

theorem child_FP (right : Bool) : child right ∈ FP := by
  have hi := mem_FP_comp (mem_FP_comp indexWord_FP (cons_mem_FP right)) BinaryNat.normalize_mem_FP
  have hh := drop_mem_FP heightWord_FP (UnaryFn.const 1)
  have h := mem_FP_pair original_FP (mem_FP_pair hh hi)
  exact mem_FP_of_eq h (fun p => by simp only [child, Function.comp_apply])

theorem original_packet (c : List Bool) (h i : ℕ) : original (packet c h i) = c := by
  simp only [original, packet, pairFst_pair]

theorem height_packet (c : List Bool) (h i : ℕ) : height (packet c h i) = h := by
  simp only [height, heightWord, packet, pairSnd_pair, pairFst_pair, List.length_replicate]

theorem index_packet (c : List Bool) (h i : ℕ) : index (packet c h i) = i := by
  simp only [index, indexWord, packet, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem original_child (right : Bool) (p : List Bool) : original (child right p) = original p := by
  simp only [original, child, pairFst_pair]

theorem height_child (right : Bool) (p : List Bool) : height (child right p) = height p - 1 := by
  simp only [height, heightWord, child, pairFst_pair, pairSnd_pair, List.length_drop]

theorem index_child (right : Bool) (p : List Bool) :
    index (child right p) = 2 * index p + if right then 1 else 0 := by
  simp only [index, indexWord, child, pairSnd_pair, BinaryNat.normalize_eq_bits,
    Nat.fromBitsLE_bits, Nat.fromBitsLE_cons]
  cases right <;> simp [Nat.add_comm]

theorem child_packet (right : Bool) (c : List Bool) (h i : ℕ) :
    child right (packet c (h + 1) i) = packet c h (2 * i + if right then 1 else 0) := by
  simp only [child, original, heightWord, indexWord, packet, pairFst_pair, pairSnd_pair,
    List.drop_replicate, Nat.add_sub_cancel, BinaryNat.normalize_eq_bits, BinaryNatCode.encode,
    Nat.fromBitsLE_cons, Nat.fromBitsLE_bits]
  cases right <;> simp [Nat.mul_comm, Nat.add_comm]

theorem packet_length (c : List Bool) (h i : ℕ) :
    (packet c h i).length = 2 * c.length + 2 * h + i.size + 4 := by
  simp only [packet, pair_length, List.length_replicate, BinaryNatCode.length_encode]
  omega

def Paired (p : List Bool) : Prop := p = pair (original p) (pair (heightWord p) (indexWord p))

theorem paired_packet (c : List Bool) (h i : ℕ) : Paired (packet c h i) := by
  simp only [Paired, original, packet, heightWord, indexWord, pairFst_pair, pairSnd_pair]

theorem paired_child (right : Bool) (p : List Bool) : Paired (child right p) := by
  simp only [Paired, child, original, heightWord, indexWord, pairFst_pair, pairSnd_pair]

theorem child_length_lt (right : Bool) (p : List Bool) (hp : Paired p) (hh : 0 < height p) :
    (child right p).length < p.length := by
  have hl := congrArg List.length hp
  simp only [pair_length] at hl
  have hi := BinaryNat.normalize_length_le (right :: indexWord p)
  simp only [List.length_cons] at hi
  simp only [child, pair_length, List.length_drop]
  dsimp only [height] at hh
  omega

theorem height_le_length (p : List Bool) : height p ≤ p.length :=
  (pairFst_length_le (pairSnd p)).trans (pairSnd_length_le p)

noncomputable def node (leaves : List Bool → ℕ → SeparableIntegerPolynomial) (p : List Bool) :
    SeparableIntegerPolynomial := BalancedPrimitiveTree.node (leaves (original p)) (height p) (index p)

theorem node_packet (leaves : List Bool → ℕ → SeparableIntegerPolynomial) (c : List Bool) (h i : ℕ) :
    node leaves (packet c h i) = BalancedPrimitiveTree.node (leaves c) h i := by
  simp only [node, original_packet, height_packet, index_packet]

theorem node_children (leaves : List Bool → ℕ → SeparableIntegerPolynomial) (p : List Bool) (hh : 0 < height p) :
    node leaves p = (node leaves (child false p)).combine (node leaves (child true p)) := by
  obtain ⟨h, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
  simp only [node, original_child, height_child, index_child, he, Nat.succ_sub_one,
    Bool.false_eq_true, ite_false, ite_true, Nat.add_zero, BalancedPrimitiveTree.node]

theorem node_finite_parameter (p : List Bool → ℕ → Polynomial ℤ) (count : List Bool → ℕ)
    (hne : ∀ c i, i < count c → p c i ≠ 0) (c : List Bool) :
    node (fun c => FiniteAnnihilatorTree.leaf (p c) (count c) (hne c)) (packet c (count c).size 0) =
      FiniteAnnihilatorTree.parameter (p c) (count c) (hne c) :=
  node_packet _ c (count c).size 0

end LeanCanny.Algebra.BalancedParameterContext

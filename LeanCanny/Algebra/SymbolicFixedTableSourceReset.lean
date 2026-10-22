/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SymbolicFixedTableTaskBounds

/-! # Symbolic source requests rebuild polynomially bounded task words -/
@[expose] public section
set_option maxRecDepth 256
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

namespace LeanCanny.Algebra.SymbolicFixedTableTaskRouting
open LeanCanny.Encoding LeanCanny.Computation SymbolicFixedTableEntryBits
open BerkowitzPolynomial.TaskDispatch

theorem coefficientTask_length (right : Bool) (p : List Bool) :
    (coefficientTask right p).length =
      4 * (BalancedParameterContext.child right (sourceNode p)).length + 4 * (sourceAlpha p).length +
        2 * (pairSnd p).length + (pairSnd (pairFst p)).length + 12 := by
  simp only [coefficientTask, Function.comp_apply, determinantTask, tag, List.length_cons,
    childInput, matrixPacket, pair_length]
  omega

theorem sourceAlpha_length_le_left (F : Family) (B : List Bool → List Bool) (p : List Bool)
    (hB : 0 < Nat.fromBitsLE (B (pairFst p))) :
    (sourceAlpha (CannyResultantBits.RecursiveStage.leftQuery F.access (sourceInput B p))).length ≤
      (Nat.fromBitsLE (B (pairFst p))).size := by
  rw [sourceAlpha_leftQuery, BinaryNat.mod_pair, Nat.size_eq_bits_len]
  exact Nat.size_le_size (Nat.mod_lt _ hB).le

theorem sourceAlpha_length_le_right (B : List Bool → List Bool) (p : List Bool)
    (hB : 0 < Nat.fromBitsLE (B (pairFst p))) :
    (sourceAlpha (CannyResultantBits.RecursiveStage.rightQuery (sourceInput B p))).length ≤
      (Nat.fromBitsLE (B (pairFst p))).size := by
  rw [sourceAlpha_rightQuery, BinaryNat.mod_pair, Nat.size_eq_bits_len]
  exact Nat.size_le_size (Nat.mod_lt _ hB).le

end LeanCanny.Algebra.SymbolicFixedTableTaskRouting

namespace LeanCanny.Algebra.SymbolicFixedTableTreeSource
open LeanCanny.Encoding LeanCanny.Computation
open Polynomial SymbolicScaledSquarefree SymbolicFixedTableEntryBits
open SymbolicFixedTableTaskRouting BerkowitzPolynomial.TaskDispatch

variable (L : List Bool → Polynomial Coefficient) (E : List Bool → ℕ)
  (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)

attribute [local irreducible] BinaryNat.normalize BinaryNat.add BinaryNat.sub BinaryNat.mul
  BinaryNat.div BinaryNat.mod CannyResultantBits.RecursiveStage.selectRight
  CannyResultantBits.RecursiveStage.active CannyResultantBits.RecursiveStage.leftQuery
  CannyResultantBits.RecursiveStage.rightQuery selectedDegree family leftOrder rightOrder
  BalancedMetadataTable.read BalancedMetadataTable.order BalancedParameterContext.child

def sourceResetBound (R : List Bool → ℕ) (root : List Bool) : ℕ :=
  root.length + 4 * (5 * root.length + 4) + 4 * R root +
    2 * (5 * root.length + 4 + selectedDegreeBound E R root + 1) + root.length + 12

theorem sourceResetBound_unary (hE : BinaryFn E) (R : List Bool → ℕ) (hR : UnaryFn R) :
    UnaryFn (sourceResetBound E R) := by
  have hn := UnaryFn.length id_mem_FP
  have hnode := ((UnaryFn.const 5).mul hn).add (UnaryFn.const 4)
  have hs := (hn.add ((UnaryFn.const 4).mul hnode)).add ((UnaryFn.const 4).mul hR)
  have hd := (UnaryFn.const 2).mul ((hnode.add (selectedDegreeBound_unary E hE R hR)).add (UnaryFn.const 1))
  exact (((hs.add hd).add hn).add (UnaryFn.const 12))

theorem source_request_length_le (R : List Bool → ℕ)
    (hR : ∀ root q, tasks L E hL root q → (radix E (origin q)).size ≤ R root)
    (root q child : List Bool) (hq : tasks L E hL root q)
    (h : Requests (access L E hL) (program L E hL).controller (fun _ => 1) q child)
    (hs : SelectedSource q) : child.length ≤ sourceResetBound E R root := by
  obtain ⟨hl, hn, he⟩ := request_source L E hL q child h hs
  have ha := CannyResultantBits.RecursiveStage.request_active (source L).access _ hn
  have hc : tasks L E hL root child := hq.tail h
  have hnode := reachable_node_length_le L E hL root child hc
  have hparent := reachable_node_length_le L E hL root q hq
  have hmod := reachable_modulusWord_length_le L E hL root q hq
  have hr := hR root q hq
  have hd := reachable_selectedDegree_size_le L E hL R hR root q hq
  have ho : origin q = pairFst (payload q) := by
    obtain ⟨hz, hd, hf, hm⟩ := hs
    simp only [origin, hz, hd, hf, hm, Bool.false_eq_true, ite_false]
  have hdegree : selectedDegree (family L E) q = Nat.fromBitsLE (entryDegree (payload q)) := by
    obtain ⟨hz, hd, hf, hm⟩ := hs
    simp only [selectedDegree, entryDegree, hz, hd, hf, hm, Bool.false_eq_true, ite_false]
  rw [ho] at hparent hmod hr
  rw [hdegree] at hd
  have hB : 0 < Nat.fromBitsLE (BinaryNatCode.encode (radix E (pairFst (payload q)))) := by
    rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    unfold radix
    omega
  rw [he] at hnode ⊢
  cases hright : CannyResultantBits.RecursiveStage.selectRight (source L).access
    (sourceInput (fun q => BinaryNatCode.encode (radix E q)) (payload q)) with
  | true =>
    simp only [hright, ite_true] at hnode ⊢
    have halpha := sourceAlpha_length_le_right (fun q => BinaryNatCode.encode (radix E q)) (payload q) hB
    rw [BinaryNatCode.encode, Nat.fromBitsLE_bits] at halpha
    have htheta := rightQuery_root_length_le (source L) (fun q => BinaryNatCode.encode (radix E q)) (payload q) ha hright
    have horder := (rightOrder_size_le (pairFst (payload q))).trans hparent
    have horder' : ((source L).rightOrder (pairFst (pairFst (payload q)))).size ≤ 5 * root.length + 4 := horder
    have hm := congrArg List.length (rightQuery_modulusWord E (payload q))
    simp only [coefficientTask, Function.comp_apply, origin_determinant, childInput, matrixPacket,
      nodeContext, pairFst_pair] at hnode
    simp only [coefficientTask, Function.comp_apply, origin_determinant, childInput, matrixPacket, pairSnd_pair] at hm
    rw [coefficientTask_length]
    unfold sourceResetBound
    omega
  | false =>
    simp only [hright, Bool.false_eq_true, ite_false] at hnode ⊢
    have halpha := sourceAlpha_length_le_left (source L) (fun q => BinaryNatCode.encode (radix E q)) (payload q) hB
    rw [BinaryNatCode.encode, Nat.fromBitsLE_bits] at halpha
    have htheta := leftQuery_root_length_le (source L) (fun q => BinaryNatCode.encode (radix E q)) (payload q) ha hright
    have horder := (leftOrder_size_le (pairFst (payload q))).trans hparent
    have horder' : ((source L).leftOrder (pairFst (pairFst (payload q)))).size ≤ 5 * root.length + 4 := horder
    have hm := congrArg List.length (leftQuery_modulusWord L E (payload q))
    simp only [coefficientTask, Function.comp_apply, origin_determinant, childInput, matrixPacket,
      nodeContext, pairFst_pair] at hnode
    simp only [coefficientTask, Function.comp_apply, origin_determinant, childInput, matrixPacket, pairSnd_pair] at hm
    rw [coefficientTask_length]
    unfold sourceResetBound
    omega

end LeanCanny.Algebra.SymbolicFixedTableTreeSource

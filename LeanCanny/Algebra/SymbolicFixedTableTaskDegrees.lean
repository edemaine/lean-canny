/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SymbolicFixedTableTaskGraph
public import LeanCanny.Algebra.CannyResultantTaskDegrees
public import LeanCanny.Algebra.BerkowitzTaskDegrees

/-! # Binary degree growth in the symbolic coefficient graph -/
@[expose] public section
set_option maxRecDepth 256
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

namespace LeanCanny.Algebra.SymbolicFixedTableTaskRouting
open LeanCanny.Encoding LeanCanny.Computation SymbolicFixedTableEntryBits

theorem sourceAlpha_leftQuery (F : Family) (B : List Bool → List Bool) (p : List Bool) :
    sourceAlpha (CannyResultantBits.RecursiveStage.leftQuery F.access (sourceInput B p)) =
      BinaryNat.mod (pair (entryDegree p) (B (pairFst p))) := by
  unfold sourceAlpha
  rw [CannyResultantBits.RecursiveStage.leftQuery_context]
  simp only [sourceInput, Function.comp_apply, entryQuery, splitInput, pairFst_pair, pairSnd_pair]

theorem sourceAlpha_rightQuery (B : List Bool → List Bool) (p : List Bool) :
    sourceAlpha (CannyResultantBits.RecursiveStage.rightQuery (sourceInput B p)) =
      BinaryNat.mod (pair (entryDegree p) (B (pairFst p))) := by
  unfold sourceAlpha
  rw [CannyResultantBits.RecursiveStage.rightQuery_context]
  simp only [sourceInput, Function.comp_apply, entryQuery, splitInput, pairFst_pair, pairSnd_pair]

theorem sourceInput_degree (B : List Bool → List Bool) (p : List Bool) :
    SylvesterPolynomialBits.RecursiveStage.coefficientDegree (sourceInput B p) =
      Nat.fromBitsLE (entryDegree p) / Nat.fromBitsLE (B (pairFst p)) := by
  simp only [SylvesterPolynomialBits.RecursiveStage.coefficientDegree, sourceInput, Function.comp_apply,
    entryQuery, splitInput, pairSnd_pair, BinaryNat.div_pair, Nat.fromBitsLE_bits]

theorem leftQuery_root_length_le (F : Family) (B : List Bool → List Bool) (p : List Bool)
    (ha : CannyResultantBits.RecursiveStage.active F.access (sourceInput B p) = true)
    (hs : CannyResultantBits.RecursiveStage.selectRight F.access (sourceInput B p) = false) :
    (pairSnd (CannyResultantBits.RecursiveStage.leftQuery F.access (sourceInput B p))).length ≤
      (F.leftOrder (pairFst (pairFst p))).size + (Nat.fromBitsLE (entryDegree p)).size + 1 := by
  have h := CannyResultantBits.RecursiveStage.leftQuery_degree_length_le F.access _ ha hs
  apply h.trans
  rw [sourceInput_degree]
  simp only [sourceInput, Function.comp_apply, entryQuery, splitInput, pairFst_pair, pairSnd_pair]
  have hd := Nat.size_le_size (Nat.div_le_self (Nat.fromBitsLE (entryDegree p)) (Nat.fromBitsLE (B (pairFst p))))
  omega

theorem rightQuery_root_length_le (F : Family) (B : List Bool → List Bool) (p : List Bool)
    (ha : CannyResultantBits.RecursiveStage.active F.access (sourceInput B p) = true)
    (hs : CannyResultantBits.RecursiveStage.selectRight F.access (sourceInput B p) = true) :
    (pairSnd (CannyResultantBits.RecursiveStage.rightQuery (sourceInput B p))).length ≤
      (F.rightOrder (pairFst (pairFst p))).size := by
  have h := CannyResultantBits.RecursiveStage.rightQuery_degree_length_le F.access _ ha hs
  apply h.trans_eq
  simp only [sourceInput, Function.comp_apply, entryQuery, splitInput, pairFst_pair, pairSnd_pair]

end LeanCanny.Algebra.SymbolicFixedTableTaskRouting

namespace LeanCanny.Algebra.SymbolicFixedTableTreeSource
open LeanCanny.Encoding LeanCanny.Computation
open Polynomial SymbolicScaledSquarefree SymbolicFixedTableEntryBits
open SymbolicFixedTableTaskRouting BerkowitzPolynomial.TaskDispatch
attribute [local irreducible] BinaryNat.normalize BinaryNat.add BinaryNat.sub BinaryNat.mul
  BinaryNat.div BinaryNat.mod CannyResultantBits.RecursiveStage.selectRight
  CannyResultantBits.RecursiveStage.active CannyResultantBits.RecursiveStage.leftQuery
  CannyResultantBits.RecursiveStage.rightQuery
variable (L : List Bool → Polynomial Coefficient) (E : List Bool → ℕ)
  (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)

private theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (Nat.lt_size_self b).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (pow_pos (by decide) _))

private theorem size_add_le (a b : ℕ) : (a + b).size ≤ a.size + b.size + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ (a.size + b.size) := (Nat.lt_size_self a).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hb : b < 2 ^ (a.size + b.size) := (Nat.lt_size_self b).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  rw [pow_succ]
  omega

theorem family_degree_le (q : List Bool) : (family L E).degree q ≤ degree E q := by
  change (if high E q then 0 else if isLeaf q then degree E q else degree E q) ≤ degree E q
  split_ifs <;> omega

theorem family_degree_size_le (q : List Bool) :
    ((family L E).degree q).size ≤ (alpha q).size + (radix E q).size + (theta q).size + 1 := by
  exact (Nat.size_le_size (family_degree_le L E q)).trans
    ((size_add_le _ _).trans (by have := size_mul_le (radix E q) (theta q); omega))

theorem radixSizeBound_exists (hE : BinaryFn E) :
    ∃ R : List Bool → ℕ, UnaryFn R ∧ ∀ root q, tasks L E hL root q → (radix E (origin q)).size ≤ R root := by
  have hf : BinaryFn (fun p => SymbolicFixedTablePolynomialTree.nodeBound E p + 1) :=
    (SymbolicFixedTablePolynomialTree.nodeBound_binary E hE).add (BinaryFn.const 1)
  have hn : UnaryFn (fun root : List Bool => 5 * root.length + 4) :=
    ((UnaryFn.const 5).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 4)
  obtain ⟨R, hR, hb⟩ := hf.inputSizeEnvelope hn
  exact ⟨R, hR, fun root q hq => hb root (nodeContext (origin q)) (reachable_node_length_le L E hL root q hq)⟩

theorem coefficientTask_degree_size_le (right : Bool) (p : List Bool) :
    (selectedDegree (family L E) (coefficientTask right p)).size ≤
      (Nat.fromBitsLE (sourceAlpha p)).size + (radix E (childInput right p)).size +
        (Nat.fromBitsLE (pairSnd p)).size + 1 := by
  change ((family L E).degree (childInput right p)).size ≤ _
  have h := family_degree_size_le L E (childInput right p)
  simpa only [alpha, theta, childInput, matrixPacket, pairFst_pair, pairSnd_pair] using h

private theorem order_size_le (p : List Bool) :
    (BalancedMetadataTable.order p).size ≤ BalancedMetadataTable.width (BalancedParameterContext.original p) :=
  (Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length _)).trans (BalancedMetadataTable.read_length_le false p)

theorem leftOrder_size_le (c : List Bool) : (leftOrder (pairFst c)).size ≤ (nodeContext c).length := by
  have h := order_size_le (BalancedParameterContext.child false (nodeContext c))
  rw [BalancedParameterContext.original_child] at h
  exact h.trans ((BalancedMetadataTable.width_le_length _).trans (pairFst_length_le _))

theorem rightOrder_size_le (c : List Bool) : (rightOrder (pairFst c)).size ≤ (nodeContext c).length := by
  have h := order_size_le (BalancedParameterContext.child true (nodeContext c))
  rw [BalancedParameterContext.original_child] at h
  exact h.trans ((BalancedMetadataTable.width_le_length _).trans (pairFst_length_le _))

theorem sourceAlpha_size_le_left (p : List Bool) :
    (Nat.fromBitsLE (sourceAlpha (CannyResultantBits.RecursiveStage.leftQuery (source L).access
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))).size ≤ (radix E (pairFst p)).size := by
  rw [sourceAlpha_leftQuery, BinaryNat.mod_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.fromBitsLE_bits]
  exact Nat.size_le_size (Nat.mod_lt _ (show 0 < radix E (pairFst p) by unfold radix; omega)).le

theorem sourceAlpha_size_le_right (p : List Bool) :
    (Nat.fromBitsLE (sourceAlpha (CannyResultantBits.RecursiveStage.rightQuery
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))).size ≤ (radix E (pairFst p)).size := by
  rw [sourceAlpha_rightQuery, BinaryNat.mod_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.fromBitsLE_bits]
  exact Nat.size_le_size (Nat.mod_lt _ (show 0 < radix E (pairFst p) by unfold radix; omega)).le

private theorem decoded_size_le (w : List Bool) : (Nat.fromBitsLE w).size ≤ w.length :=
  Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length w)

attribute [local irreducible] selectedDegree family leftOrder rightOrder
  BalancedMetadataTable.read BalancedMetadataTable.order BalancedParameterContext.child

theorem leftQuery_degree_size_le (p : List Bool) (R O : ℕ)
    (ha : CannyResultantBits.RecursiveStage.active (source L).access
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p) = true)
    (hs : CannyResultantBits.RecursiveStage.selectRight (source L).access
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p) = false)
    (hp : (radix E (pairFst p)).size ≤ R)
    (hc : (radix E (childInput false (CannyResultantBits.RecursiveStage.leftQuery (source L).access
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))).size ≤ R)
    (ho : (leftOrder (pairFst (pairFst p))).size ≤ O) :
    (selectedDegree (family L E) (coefficientTask false (CannyResultantBits.RecursiveStage.leftQuery (source L).access
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))).size ≤
        (Nat.fromBitsLE (entryDegree p)).size + 2 * R + O + 2 := by
  have h := coefficientTask_degree_size_le L E false (CannyResultantBits.RecursiveStage.leftQuery (source L).access
    (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p))
  have halpha := (sourceAlpha_size_le_left L E p).trans hp
  have htheta := (decoded_size_le _).trans
    (leftQuery_root_length_le (source L) (fun q => BinaryNatCode.encode (radix E q)) p ha hs)
  have ho' : ((source L).leftOrder (pairFst (pairFst p))).size ≤ O := ho
  omega

theorem rightQuery_degree_size_le (p : List Bool) (R O : ℕ)
    (ha : CannyResultantBits.RecursiveStage.active (source L).access
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p) = true)
    (hs : CannyResultantBits.RecursiveStage.selectRight (source L).access
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p) = true)
    (hp : (radix E (pairFst p)).size ≤ R)
    (hc : (radix E (childInput true (CannyResultantBits.RecursiveStage.rightQuery
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))).size ≤ R)
    (ho : (rightOrder (pairFst (pairFst p))).size ≤ O) :
    (selectedDegree (family L E) (coefficientTask true (CannyResultantBits.RecursiveStage.rightQuery
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))).size ≤
        (Nat.fromBitsLE (entryDegree p)).size + 2 * R + O + 2 := by
  have h := coefficientTask_degree_size_le L E true (CannyResultantBits.RecursiveStage.rightQuery
    (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p))
  have halpha := (sourceAlpha_size_le_right E p).trans hp
  have htheta := (decoded_size_le _).trans
    (rightQuery_root_length_le (source L) (fun q => BinaryNatCode.encode (radix E q)) p ha hs)
  have ho' : ((source L).rightOrder (pairFst (pairFst p))).size ≤ O := ho
  omega

def initialDegreeSizeBound (q : List Bool) : ℕ := q.length + (degree E (payload q)).size

theorem initialDegreeSizeBound_unary (hE : BinaryFn E) : UnaryFn (initialDegreeSizeBound E) := by
  have hd : UnaryFn (fun q => (degree E q).size) :=
    (UnaryFn.length (degree_binary E hE).bits_mem_FP).of_eq (fun q => Nat.size_eq_bits_len _)
  exact (UnaryFn.length id_mem_FP).add (hd.comp payload_FP)

theorem selectedDegree_root_size_le (q : List Bool) :
    (selectedDegree (family L E) q).size ≤ initialDegreeSizeBound E q := by
  have hp : (payload q).length ≤ q.length := by simp only [payload, List.length_drop]; omega
  have hs := (pairSnd_length_le (payload q)).trans hp
  have hsss := (pairSnd_length_le (pairSnd (pairSnd (payload q)))).trans
    ((pairSnd_length_le _).trans ((pairSnd_length_le _).trans hp))
  unfold selectedDegree initialDegreeSizeBound
  split_ifs
  · simp only [Nat.size_zero]; omega
  · have h := Nat.size_le_size (family_degree_le L E (payload q)); omega
  · exact (decoded_size_le _).trans (by omega)
  · exact (decoded_size_le _).trans (by omega)
  · exact (decoded_size_le _).trans (by omega)

end LeanCanny.Algebra.SymbolicFixedTableTreeSource

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedTableTaskDegrees

/-! # A common polynomial bound on reachable matrix contexts

Source requests rebuild their matrix context from a bounded node address,
a canonical coefficient degree, and the inherited modulus word. Internal
requests retain that context or request zero. Thus recursion does not nest
or repeatedly multiply the size of the matrix context.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedTablePolynomials
open LeanCanny.Encoding LeanCanny.Computation
open BerkowitzPolynomial.TaskDispatch CannyBalancedTaskRouting

attribute [local irreducible] BinaryNat.normalize BinaryNat.add BinaryNat.sub BinaryNat.mul
  BinaryNat.div BinaryNat.mod tree node BalancedMetadataTable.read

private theorem coefficientTask_context_length (B : SeparableBits.Family) (right : Bool) (p : List Bool)
    (hc : pairSnd p = BinaryNatCode.encode (Nat.fromBitsLE (pairSnd p))) :
    (origin (coefficientTask right p)).length =
      4 * (nodeContext (origin (coefficientTask right p))).length +
      2 * (selectedDegree (matrixFamily B) (coefficientTask right p)).size +
      (pairSnd (origin (coefficientTask right p))).length + 6 := by
  have hd : (pairSnd p).length = (Nat.fromBitsLE (pairSnd p)).size := by
    conv_lhs => rw [hc]
    rw [BinaryNatCode.length_encode]
  rw [selectedDegree_coefficientTask]
  simp only [coefficientTask, Function.comp_apply, origin_determinant, nodeContext, childInput,
    matrixPacket, pairFst_pair, pairSnd_pair, pair_length]
  omega

theorem source_request_context_length (B : SeparableBits.Family) (q child : List Bool)
    (h : Requests (matrixAccess B)
      (CannyResultantBits.WithSquarefreeLeaves.program (leafFamily B) (sourceAccess B) isLeaf
        (coefficientTask false) (coefficientTask true)).controller (fun _ => 1) q child)
    (hs : SelectedSource q) :
    (origin child).length = 4 * (nodeContext (origin child)).length +
      2 * (selectedDegree (matrixFamily B) child).size + (pairSnd (origin child)).length + 6 := by
  obtain ⟨_, _, he⟩ := request_source (leafFamily B) (sourceAccess B) q child h hs
  rw [he]
  split_ifs
  · apply coefficientTask_context_length
    simp only [CannyResultantBits.RecursiveStage.rightQuery_degree_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · apply coefficientTask_context_length
    simp only [CannyResultantBits.RecursiveStage.leftQuery_degree_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]

def contextBound (root : List Bool) : ℕ :=
  4 * (5 * root.length + 4) + 2 * (root.length + (root.length + 1) * root.length) + root.length + 6

theorem contextBound_unary : UnaryFn contextBound := by
  have hn := UnaryFn.length id_mem_FP
  exact (((UnaryFn.const 4).mul (((UnaryFn.const 5).mul hn).add (UnaryFn.const 4))).add
    ((UnaryFn.const 2).mul (hn.add ((hn.add (UnaryFn.const 1)).mul hn)))).add hn |>.add (UnaryFn.const 6)

theorem reachable_context_length_le (B : SeparableBits.Family) (root q : List Bool) (hq : reachableTasks B root q) :
    (origin q).length ≤ contextBound root := by
  change Relation.ReflTransGen _ root q at hq
  induction hq with
  | refl =>
    have h := origin_length_le root
    dsimp only [contextBound]
    omega
  | @tail q child hq hstep ih =>
    by_cases hs : SelectedSource q
    · have hc : reachableTasks B root child := hq.tail hstep
      have hn := CannyBalancedTaskRouting.reachable_node_length_le (leafFamily B) (sourceAccess B) root child hc
      have hm := CannyBalancedTaskRouting.reachable_modulusWord_length_le (leafFamily B) (sourceAccess B) root child hc
      have hd := reachable_degree_size_le B root child hc
      have hl := source_request_context_length B q child hstep hs
      dsimp only [contextBound]
      omega
    · obtain ⟨t, _, _, hn, he⟩ := hstep
      rcases internal_query_origin (CannyResultantBits.WithSquarefreeLeaves.access (leafFamily B) (sourceAccess B) isLeaf)
        _ _ q t hn hs with he0 | heo
      · rw [he, he0, origin_zero]
        exact Nat.zero_le _
      · rw [he, heo]
        exact ih

end LeanCanny.Algebra.BalancedTablePolynomials

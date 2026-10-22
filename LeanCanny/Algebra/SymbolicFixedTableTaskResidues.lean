/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableTaskGraph
public import LeanCanny.Algebra.SymbolicFixedTableEntryResidues
public import LeanCanny.Algebra.CannyBalancedTaskResidues

/-! # Every symbolic task reply inherits the root modulus bound -/

@[expose] public section
set_option maxRecDepth 256
set_option backward.isDefEq.respectTransparency false
namespace LeanCanny.Algebra.SymbolicFixedTableTreeSource
open LeanCanny.Encoding LeanCanny.Computation
open Polynomial SymbolicScaledSquarefree SymbolicFixedTableEntryBits
open SymbolicFixedTableTaskRouting BerkowitzPolynomial.TaskDispatch

variable (L : List Bool → Polynomial Coefficient) (E : List Bool → ℕ)
  (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)

theorem family_modulus (q : List Bool) : (family L E).modulus q = CannyResultantBits.mValue q := by
  change (if high E q then Nat.fromBitsLE (pairSnd q) + 1 else
    if isLeaf q then Nat.fromBitsLE (pairSnd q) + 1 else Nat.fromBitsLE (pairSnd q) + 1) = _
  split_ifs <;> rfl

theorem entry_length_le (q : List Bool) :
    ((access L E hL).entry q).length ≤ ((family L E).modulus (pairFst q)).size := by
  rw [family_modulus]
  change (if high E (pairFst q) then [] else if isLeaf (pairFst q) then
    (leafAccess L E hL).entry q else (pairAccess L E hL).entry q).length ≤ _
  split_ifs
  · exact Nat.zero_le _
  · have h := coefficient_length_le (leafPolynomial L) (SymbolicFixedTableScalarMatrix.query (radix E) q)
    simpa only [leafAccess, SymbolicFixedTableScalarMatrix.access, Function.comp_apply,
      SymbolicFixedTableScalarMatrix.query, CannyResultantBits.mValue, pairFst_pair, pairSnd_pair] using h
  · rw [pairAccess, Family.encodedMatrixAccess_entry]
    exact (source L).encodedEntry_length_le (fun q => BinaryNatCode.encode (radix E q)) q

theorem leftQuery_modulus (p : List Bool) :
    CannyResultantBits.mValue (origin (coefficientTask false (CannyResultantBits.RecursiveStage.leftQuery (source L).access
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))) = CannyResultantBits.mValue (pairFst p) := by
  simp only [coefficientTask, Function.comp_apply, origin_determinant, childInput, matrixPacket,
    CannyResultantBits.mValue, pairSnd_pair]
  rw [CannyResultantBits.RecursiveStage.leftQuery_context]
  simp only [sourceInput, Function.comp_apply, entryQuery, splitInput, pairFst_pair, pairSnd_pair]

theorem rightQuery_modulus (p : List Bool) :
    CannyResultantBits.mValue (origin (coefficientTask true (CannyResultantBits.RecursiveStage.rightQuery
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))) = CannyResultantBits.mValue (pairFst p) := by
  simp only [coefficientTask, Function.comp_apply, origin_determinant, childInput, matrixPacket,
    CannyResultantBits.mValue, pairSnd_pair]
  rw [CannyResultantBits.RecursiveStage.rightQuery_context]
  simp only [sourceInput, Function.comp_apply, entryQuery, splitInput, pairFst_pair, pairSnd_pair]

theorem reachable_modulus_le (root q : List Bool) (hq : tasks L E hL root q) :
    CannyResultantBits.mValue (origin q) ≤ CannyResultantBits.mValue (origin root) :=
  reachable_measure_le L E hL CannyResultantBits.mValue
    (fun c => by change 1 ≤ Nat.fromBitsLE (pairSnd c) + 1; omega)
    (fun p _ => (leftQuery_modulus L E p).le) (fun p _ => (rightQuery_modulus E p).le) root q hq

theorem reachable_answer_length_le (root q : List Bool) (hq : tasks L E hL root q) :
    (answer (access L E hL) q).length ≤ root.length + 1 := by
  have h := answer_length_le (access L E hL) (entry_length_le L E hL) q
  rw [family_modulus] at h
  exact h.trans ((Nat.size_le_size (reachable_modulus_le L E hL root q hq)).trans
    ((CannyBalancedTaskRouting.modulus_size_le (origin root)).trans
      (Nat.add_le_add_right (origin_length_le root) 1)))

theorem leftQuery_modulusWord (p : List Bool) :
    pairSnd (origin (coefficientTask false (CannyResultantBits.RecursiveStage.leftQuery (source L).access
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))) = pairSnd (pairFst p) := by
  simp only [coefficientTask, Function.comp_apply, origin_determinant, childInput, matrixPacket, pairSnd_pair]
  rw [CannyResultantBits.RecursiveStage.leftQuery_context]
  simp only [sourceInput, Function.comp_apply, entryQuery, splitInput, pairFst_pair, pairSnd_pair]

theorem rightQuery_modulusWord (p : List Bool) :
    pairSnd (origin (coefficientTask true (CannyResultantBits.RecursiveStage.rightQuery
      (sourceInput (fun q => BinaryNatCode.encode (radix E q)) p)))) = pairSnd (pairFst p) := by
  simp only [coefficientTask, Function.comp_apply, origin_determinant, childInput, matrixPacket, pairSnd_pair]
  rw [CannyResultantBits.RecursiveStage.rightQuery_context]
  simp only [sourceInput, Function.comp_apply, entryQuery, splitInput, pairFst_pair, pairSnd_pair]

theorem reachable_modulusWord_length_le (root q : List Bool) (hq : tasks L E hL root q) :
    (pairSnd (origin q)).length ≤ root.length := by
  have hm := reachable_measure_le L E hL (fun c => (pairSnd c).length) (fun _ => Nat.zero_le _)
    (fun p _ => by rw [leftQuery_modulusWord L E]) (fun p _ => by rw [rightQuery_modulusWord E]) root q hq
  exact hm.trans ((pairSnd_length_le _).trans (origin_length_le root))

end LeanCanny.Algebra.SymbolicFixedTableTreeSource

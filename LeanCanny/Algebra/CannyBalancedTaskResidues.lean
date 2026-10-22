/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyBalancedTaskRanks
public import LeanCanny.Algebra.BerkowitzTaskResidues

/-! # The balanced coefficient graph preserves its modulus

Internal requests retain the original matrix context or request zero. A
resultant source replaces the node address while retaining the modulus word.
Consequently every reachable modulus has at most `root.length + 1` bits,
including malformed external roots and arbitrary supplied metadata tables.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyBalancedTaskRouting
open LeanCanny.Encoding LeanCanny.Computation
open BerkowitzPolynomial.TaskDispatch
open CannyResultantBits (mValue)

theorem coefficientTask_modulus (right : Bool) (p : List Bool) :
    mValue (origin (coefficientTask right p)) = mValue (pairFst p) := by
  simp only [coefficientTask, Function.comp_apply, origin_determinant, childInput, matrixPacket,
    mValue, pairSnd_pair]

theorem modulus_size_le (c : List Bool) : (mValue c).size ≤ c.length + 1 := by
  have h := (BinaryNat.normalize_length_le (BinaryNat.increment (pairSnd c))).trans
    (BinaryNat.increment_length_le (pairSnd c))
  change (BinaryNat.succ (pairSnd c)).length ≤ (pairSnd c).length + 1 at h
  rw [BinaryNat.succ_eq_bits, Nat.size_eq_bits_len] at h
  exact h.trans (Nat.add_le_add_right (pairSnd_length_le c) 1)

variable (L : SeparableBits.Family) {F : CannyResultantBits.Family} {leftOrder rightOrder : List Bool → ℕ}
  (a : CannyResultantBits.Access F leftOrder rightOrder)

theorem family_modulus (c : List Bool) :
    (CannyResultantBits.WithSquarefreeLeaves.family L (F := F) isLeaf leftOrder rightOrder).modulus c = mValue c := by
  change (if isLeaf c then mValue c else mValue c) = mValue c
  split_ifs <;> rfl

attribute [local irreducible] BinaryNat.normalize BinaryNat.add BinaryNat.sub BinaryNat.succ
  BinaryNat.div BinaryNat.mod BinaryNat.mul
  SylvesterPolynomialBits.RecursiveStage.active SylvesterPolynomialBits.RecursiveStage.selectRight
  SylvesterPolynomialBits.RecursiveStage.rightInput SylvesterPolynomialBits.RecursiveStage.leftInput

theorem entry_length_le
    (hr : ∀ p, (a.rightCoefficient p).length ≤ (mValue (pairFst p)).size) (p : List Bool) :
    ((CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf).entry p).length ≤ (mValue (pairFst p)).size := by
  change (if isLeaf (pairFst p) then
    (CannyResultantBits.WithSquarefreeLeaves.leafAccess L a).entry p else a.modular.bits.entry p).length ≤ _
  split_ifs
  · have hm : ScaledQuotientBits.modulus (SeparableBits.LeafMatrix.query p) = mValue (pairFst p) := by
      simp only [ScaledQuotientBits.modulus, ScaledQuotientBits.modulusWord, SeparableBits.LeafMatrix.query,
        pairFst_pair, mValue]
    change (SeparableBits.squarefreeValue L (SeparableBits.LeafMatrix.query p)).length ≤ _
    have hb : (SeparableBits.squarefreeValue L (SeparableBits.LeafMatrix.query p)).length ≤
        (ScaledQuotientBits.modulus (SeparableBits.LeafMatrix.query p)).size := by
      let : NeZero (ScaledQuotientBits.modulus (SeparableBits.LeafMatrix.query p)) :=
        ⟨by unfold ScaledQuotientBits.modulus; omega⟩
      exact MatrixPower.residueBits_length_le _ _
    exact hm ▸ hb
  · rw [SylvesterPolynomialBits.RecursiveStage.entry_eq]
    split_ifs
    · change (a.constantCoefficient (SylvesterPolynomialBits.RecursiveStage.rightInput p)).length ≤ _
      unfold CannyResultantBits.Access.constantCoefficient
      split_ifs
      · simpa only [pairFst_pair, SylvesterPolynomialBits.RecursiveStage.rightInput_context] using
          hr (pair (pairFst (SylvesterPolynomialBits.RecursiveStage.rightInput p))
            (ShiftCoefficientBits.leftIndex (SylvesterPolynomialBits.RecursiveStage.rightInput p)))
      · exact Nat.zero_le _
    · change (F.shiftSource.value (SylvesterPolynomialBits.RecursiveStage.leftInput a.modular.bits p)).length ≤ _
      have hm : ShiftCoefficientBits.mValue (SylvesterPolynomialBits.RecursiveStage.leftInput a.modular.bits p) =
          mValue (pairFst p) := by
        simp only [ShiftCoefficientBits.mValue, ShiftCoefficientBits.modulusMinusOne,
          SylvesterPolynomialBits.RecursiveStage.leftInput_context, mValue]
      have hb : (F.shiftSource.value (SylvesterPolynomialBits.RecursiveStage.leftInput a.modular.bits p)).length ≤
          (ShiftCoefficientBits.mValue (SylvesterPolynomialBits.RecursiveStage.leftInput a.modular.bits p)).size := by
        let : NeZero (ShiftCoefficientBits.mValue (SylvesterPolynomialBits.RecursiveStage.leftInput a.modular.bits p)) :=
          ⟨by unfold ShiftCoefficientBits.mValue; omega⟩
        exact MatrixPower.residueBits_length_le _ _
      exact hm ▸ hb
    · exact Nat.zero_le _

private theorem source_query_modulus (g : List Bool → List Bool) (p : List Bool) (t : ℕ) :
    mValue (origin ((CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf
      (coefficientTask false) (coefficientTask true)).controller.query
      (((CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf
        (coefficientTask false) (coefficientTask true)).controller.reference g)^[t]
        (SingleCall.Program.initial p)))) = mValue (pairFst p) := by
  rw [CannyResultantBits.WithSquarefreeLeaves.program, SingleCall.Program.withLeaf_query_iterate]
  change mValue (origin (if CannyResultantBits.RecursiveStage.selectRight a p then
    coefficientTask true (CannyResultantBits.RecursiveStage.rightQuery p)
    else coefficientTask false (CannyResultantBits.RecursiveStage.leftQuery a p))) = _
  split_ifs
  · rw [coefficientTask_modulus, CannyResultantBits.RecursiveStage.rightQuery_context]
  · rw [coefficientTask_modulus, CannyResultantBits.RecursiveStage.leftQuery_context]

theorem request_modulus_le (q child : List Bool)
    (h : Requests (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf)
      (CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf (coefficientTask false) (coefficientTask true)).controller
      (fun _ => 1) q child) : mValue (origin child) ≤ mValue (origin q) := by
  obtain ⟨t, _, _, hn, he⟩ := h
  by_cases hs : SelectedSource q
  · obtain ⟨hz, hd, hf, hm⟩ := hs
    rw [he, query_iterate]
    simp only [hz, hd, hf, hm, Bool.false_eq_true, ite_false]
    change mValue (origin ((CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf
      (coefficientTask false) (coefficientTask true)).controller.query
      (((CannyResultantBits.WithSquarefreeLeaves.program L a isLeaf
        (coefficientTask false) (coefficientTask true)).controller.reference
          (answer (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf)))^[t]
          (SingleCall.Program.initial (payload q))))) ≤ _
    rw [source_query_modulus]
    simp only [origin, hz, hd, hf, hm, Bool.false_eq_true, ite_false]
    exact le_refl _
  · rcases internal_query_origin _ _ _ q t hn hs with hz | ho
    · rw [he, hz, origin_zero]
      change 1 ≤ Nat.fromBitsLE (pairSnd (origin q)) + 1
      omega
    · rw [he, ho]

theorem reachable_modulus_le (root q : List Bool) (hq : tasks L a root q) :
    mValue (origin q) ≤ mValue (origin root) := by
  change Relation.ReflTransGen _ root q at hq
  induction hq with
  | refl => exact le_refl _
  | @tail q child _ hstep ih => exact (request_modulus_le L a q child hstep).trans ih

theorem reachable_modulus_size_le (root q : List Bool) (hq : tasks L a root q) :
    (mValue (origin q)).size ≤ root.length + 1 :=
  (Nat.size_le_size (reachable_modulus_le L a root q hq)).trans
    ((modulus_size_le (origin root)).trans (Nat.add_le_add_right (origin_length_le root) 1))

theorem reachable_answer_length_le
    (hr : ∀ p, (a.rightCoefficient p).length ≤ (mValue (pairFst p)).size)
    (root q : List Bool) (hq : tasks L a root q) :
    (answer (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf) q).length ≤ root.length + 1 := by
  have he (p : List Bool) : ((CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf).entry p).length ≤
      ((CannyResultantBits.WithSquarefreeLeaves.family L (F := F) isLeaf leftOrder rightOrder).modulus (pairFst p)).size := by
    rw [family_modulus]
    exact entry_length_le L a hr p
  have h := answer_length_le (CannyResultantBits.WithSquarefreeLeaves.access L a isLeaf) he q
  rw [family_modulus] at h
  exact h.trans (reachable_modulus_size_le L a root q hq)

end LeanCanny.Algebra.CannyBalancedTaskRouting

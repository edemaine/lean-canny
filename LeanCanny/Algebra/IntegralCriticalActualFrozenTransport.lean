/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualScalarModels
public import LeanCanny.Algebra.IntegralCriticalTotalHeightValue
public import LeanCanny.Algebra.IntegralCriticalActualCaps
/-! # Actual retained-height replies of flat frozen power controllers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualFrozenTransport
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily IntegralCriticalFlatMatrixQuery.writer
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

noncomputable def source (F : Scripts) := (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen

theorem rank_cap (F : Scripts) (q : List Bool) :
    (source F).rank q ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q) := by
  by_cases h : valid F q
  · exact IntegralCriticalActualCaps.rank_cap F q h
  · change IntegralCriticalTotalCreatingBits.rank F q ≤ _
    rw [IntegralCriticalTotalCreatingBits.at_rank, ite_eq_right h]
    exact Nat.succ_le_of_lt (IntegralCriticalHistoryTask.numericCap_pos _ _)

theorem height_entry_fin (F : Scripts) (q : List Bool) (i : ℕ) (r t : Fin ((source F).rank q)) :
    IntegralCriticalTotalHeightBits.entry F q i r.val t.val =
      letI := (source F).ring q
      residueBits ((Algebra.leftMulMatrix ((source F).basis q) ((source F).height q i) r t : ℤ) :
        ZMod ((source F).modulus q)) := by
  rw [IntegralCriticalTotalHeightBits.entry_eq_heightAt]
  unfold IntegralCriticalScriptEulerBits.heightAt
  let := (source F).ring q
  change residueBits ((Algebra.leftMulMatrix ((source F).basis q) ((source F).height q i)
    ⟨r.val % (source F).rank q, _⟩ ⟨t.val % (source F).rank q, _⟩ : ℤ) : ZMod ((source F).modulus q)) = _
  simp only [Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt]

theorem power_height_child (F : Scripts) (q : List Bool) (r t : Fin ((source F).rank q)) :
    IntegralCriticalTotalHeightBits.value F
      (IntegralCriticalFlatMatrixQuery.writer F.toParameters .clearedHeight
        (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      residueBits ((IntegralCriticalFlatFrozenTermBits.family F.toParameters (source F)).matrix q r t) := by
  let child := IntegralCriticalFlatMatrixQuery.writer F.toParameters .clearedHeight
    (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HR : root child = root q := by
    simpa only [child, root, IntegralCriticalFlatHeightBits.root, pairFst_pair] using
      IntegralCriticalFlatMatrixQuery.writer_root F.toParameters .clearedHeight
        (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HB : IntegralCriticalHistoryTask.birth F.toParameters child = IntegralCriticalHistoryTask.birth F.toParameters q := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_birth F.toParameters .clearedHeight
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HM : IntegralCriticalHistoryTask.modulus F.toParameters child = IntegralCriticalHistoryTask.modulus F.toParameters q := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_modulus F.toParameters .clearedHeight
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HI : IntegralCriticalHistoryTask.get F.toParameters .slot8 child = IntegralCriticalHistoryTask.get F.toParameters .slot8 q := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [reduceCtorEq, ite_false, pairFst_pair]
  have HROW : IntegralCriticalHistoryTask.get F.toParameters .row child = r.val := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (r.isLt.le.trans (rank_cap F q))
  have HCOL : IntegralCriticalHistoryTask.get F.toParameters .col child = t.val := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [reduceCtorEq, ite_false, ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (t.isLt.le.trans (rank_cap F q))
  change IntegralCriticalTotalHeightBits.value F child = _
  change IntegralCriticalTotalHeightBits.entry F child
    (IntegralCriticalHistoryTask.get F.toParameters .slot8 child)
    (IntegralCriticalHistoryTask.get F.toParameters .row child) (IntegralCriticalHistoryTask.get F.toParameters .col child) = _
  rw [HI, HROW, HCOL, IntegralCriticalTotalHeightBits.entry_invariance F child q HR HB HM]
  rw [height_entry_fin]
  rfl


theorem power_replies (F : Scripts) (q : List Bool) :
    IntegralCriticalFlatFrozenTermBits.RepliesAt F.toParameters (source F)
      (IntegralCriticalTotalHeightBits.value F) q := by
  intro _ r t
  exact power_height_child F q r t

theorem sum_replies (F : Scripts) (q : List Bool) :
    IntegralCriticalFlatFrozenSumBits.RepliesAt F.toParameters (source F)
      (IntegralCriticalActualScalarModels.frozenTerm F) q := by
  intro i hi
  exact IntegralCriticalActualScalarModels.frozenSum_child_finite F q i hi

theorem constant_replies (F : Scripts) (q : List Bool) :
    IntegralCriticalFlatFrozenConstantBits.RepliesAt F.toParameters (source F)
      (IntegralCriticalActualScalarModels.frozenSum F) q := by
  intro _
  exact IntegralCriticalActualScalarModels.frozenConstant_sum_child F q

theorem sum_value (F : Scripts) (q : List Bool) :
    (IntegralCriticalFlatFrozenSumBits.program F.toParameters (source F)).value
      (IntegralCriticalActualScalarModels.frozenTerm F) q =
        IntegralCriticalActualScalarModels.frozenSum F q :=
  (IntegralCriticalFlatFrozenSumBits.value_local F.toParameters (source F)
    (IntegralCriticalActualScalarModels.frozenTerm F) q (sum_replies F q)).trans
      (IntegralCriticalActualScalarModels.frozenSum_eq F q).symm

end LeanCanny.Algebra.IntegralCriticalActualFrozenTransport

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualMonomialCoefficient
public import LeanCanny.Algebra.IntegralCriticalActualMonomialHeight
/-! # Actual leaf replies of the native flat monomial controller -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualMonomialReplies
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits IntegralCriticalActualCoefficientModel
open IntegralCriticalActualFactorModel IntegralCriticalActualLowMatrixModel
open IntegralCriticalActualMonomialCoefficient IntegralCriticalActualMonomialHeight
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap IntegralCriticalHistoryTask.phase
attribute [local irreducible] IntegralCriticalFlatMatrixQuery.writer IntegralCriticalFlatFactorQuery.writer

noncomputable def answer (F : Scripts) (q : List Bool) :=
  if IntegralCriticalHistoryTask.phase q = 2 then IntegralCriticalTotalHeightBits.value F q
  else if IntegralCriticalHistoryTask.phase q = 1 then derivative F q else original F q

theorem coefficient_matrix_child (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (q : List Bool)
    (r t : Fin ((IntegralCriticalFlatActualLow.source F).rank q))
    (hs : IntegralCriticalHistoryTask.get F.toParameters .slot8 q = 0) :
    IntegralCriticalActualMonomialCoefficient.coefficient F (IntegralCriticalFlatMatrixQuery.writer F.toParameters phase
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) = factorEntry F q 0 r.val t.val := by
  let child := IntegralCriticalFlatMatrixQuery.writer F.toParameters phase
    (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HC : IntegralCriticalHistoryTask.get F.toParameters .slot8 child = 0 := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simpa only [reduceCtorEq, ite_false, pairFst_pair] using hs
  change IntegralCriticalActualMonomialCoefficient.coefficient F child = _
  rw [← monomial_eq_coefficient F child HC]
  rw [IntegralCriticalActualFactorTransport.monomial_child F phase q r.val t.val r.isLt t.isLt, hs]

theorem coefficient_child (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F) (q : List Bool)
    (r t : Fin ((IntegralCriticalFlatActualLow.source F).rank q))
    (hs : IntegralCriticalHistoryTask.get F.toParameters .slot8 q = 0) :
    answer F (IntegralCriticalFlatGenericMonomialBits.coefficientTask F.toParameters
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
    (IntegralCriticalFlatActualLow.access F h).coefficient
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))) := by
  rw [coefficient_leaf]
  unfold IntegralCriticalFlatGenericMonomialBits.coefficientTask
  simp only [pairFst_pair]
  by_cases hx : IntegralCriticalHistoryTask.get F.toParameters .expression q = 1
  · rw [ite_eq_left hx]
    unfold answer
    rw [IntegralCriticalFlatMatrixQuery.writer_phase]
    norm_num only [IntegralCriticalHistoryTask.Phase.code, reduceCtorEq, ite_false, ite_true]
    have HC : IntegralCriticalHistoryTask.get F.toParameters .expression
        (IntegralCriticalFlatMatrixQuery.writer F.toParameters .derivativeCoefficient
          (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) = 1 := by
      rw [IntegralCriticalFlatMatrixQuery.writer_get]
      simpa only [reduceCtorEq, ite_false, pairFst_pair] using hx
    rw [← show IntegralCriticalActualMonomialCoefficient.coefficient F (IntegralCriticalFlatMatrixQuery.writer F.toParameters .derivativeCoefficient
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) = _ from ite_eq_left HC]
    exact coefficient_matrix_child F .derivativeCoefficient q r t hs
  · rw [ite_eq_right hx]
    unfold answer
    rw [IntegralCriticalFlatMatrixQuery.writer_phase]
    norm_num only [IntegralCriticalHistoryTask.Phase.code, reduceCtorEq, ite_false, ite_true]
    have HC : IntegralCriticalHistoryTask.get F.toParameters .expression
        (IntegralCriticalFlatMatrixQuery.writer F.toParameters .originalCoefficient
          (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) ≠ 1 := by
      rw [IntegralCriticalFlatMatrixQuery.writer_get]
      simpa only [reduceCtorEq, ite_false, pairFst_pair] using hx
    rw [← show IntegralCriticalActualMonomialCoefficient.coefficient F (IntegralCriticalFlatMatrixQuery.writer F.toParameters .originalCoefficient
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) = _ from ite_eq_right HC]
    exact coefficient_matrix_child F .originalCoefficient q r t hs

theorem coefficient_replies (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F) (q : List Bool) :
    IntegralCriticalFlatGenericMonomialBits.CoefficientRepliesAt F.toParameters (IntegralCriticalFlatActualLow.source F)
      (IntegralCriticalFlatActualLow.access F h) (answer F) q := by
  intro hs
  unfold IntegralCriticalFlatGenericMonomialBits.input at hs ⊢
  rw [IntegralMonomialTermBits.position_packet] at hs
  rw [IntegralMonomialTermBits.coefficientQuery_packet]
  exact coefficient_child F h q _ _ hs


theorem height_child (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F) (q : List Bool) (i : ℕ)
    (r t : Fin ((IntegralCriticalFlatActualLow.source F).rank q))
    (hi : i ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q)) :
    answer F (IntegralCriticalFlatFactorQuery.writer F.toParameters .clearedHeight (IntegralMonomialTermBits.packet q i r.val t.val)) =
    (IntegralCriticalFlatActualLow.access F h).height (IntegralMonomialTermBits.packet q i r.val t.val) := by
  let child := IntegralCriticalFlatFactorQuery.writer F.toParameters .clearedHeight (IntegralMonomialTermBits.packet q i r.val t.val)
  have HR : root child = root q := by
    simpa only [child, root, IntegralCriticalFlatHeightBits.root, IntegralMonomialTermBits.packet, pairFst_pair] using
      IntegralCriticalFlatFactorQuery.writer_root F.toParameters .clearedHeight (IntegralMonomialTermBits.packet q i r.val t.val)
  have HB : IntegralCriticalHistoryTask.birth F.toParameters child = IntegralCriticalHistoryTask.birth F.toParameters q := by
    simpa only [child, IntegralMonomialTermBits.packet, pairFst_pair] using IntegralCriticalFlatFactorQuery.writer_birth
      F.toParameters .clearedHeight (IntegralMonomialTermBits.packet q i r.val t.val)
  have HM : IntegralCriticalHistoryTask.modulus F.toParameters child = IntegralCriticalHistoryTask.modulus F.toParameters q := by
    simpa only [child, IntegralMonomialTermBits.packet, pairFst_pair] using IntegralCriticalFlatFactorQuery.writer_modulus
      F.toParameters .clearedHeight (IntegralMonomialTermBits.packet q i r.val t.val)
  have HF := IntegralCriticalFlatFactorQuery.writer_packet_fields F.toParameters .clearedHeight q i r.val t.val hi
    (r.isLt.le.trans (rank_cap F q)) (t.isLt.le.trans (rank_cap F q))
  unfold answer
  rw [IntegralCriticalFlatFactorQuery.writer_phase]
  norm_num only [IntegralCriticalHistoryTask.Phase.code, reduceCtorEq, ite_true]
  change IntegralCriticalTotalHeightBits.entry F child (IntegralCriticalHistoryTask.get F.toParameters .slot8 child)
    (IntegralCriticalHistoryTask.get F.toParameters .row child) (IntegralCriticalHistoryTask.get F.toParameters .col child) = _
  rw [HF.1, HF.2.1, HF.2.2, IntegralCriticalTotalHeightBits.entry_invariance F child q HR HB HM]
  exact (height_leaf F h q i r t).symm

theorem height_replies (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F) (q : List Bool) :
    IntegralCriticalFlatGenericMonomialBits.HeightRepliesAt F.toParameters (IntegralCriticalFlatActualLow.source F)
      (IntegralCriticalFlatActualLow.access F h) (answer F) q := by
  intro _ _
  unfold IntegralCriticalFlatGenericMonomialBits.input
  rw [IntegralMonomialTermBits.heightQuery_packet]
  exact height_child F h q _ _ _ ((Nat.sub_le _ _).trans (IntegralCriticalHistoryTask.get_le F.toParameters .slot8 q))

theorem monomial_value (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F) (q : List Bool) :
    (IntegralCriticalFlatGenericMonomialBits.program F.toParameters (IntegralCriticalFlatActualLow.source F)
      (IntegralCriticalFlatActualLow.access F h)).value (answer F)
      (IntegralCriticalFlatGenericMonomialBits.input F.toParameters (IntegralCriticalFlatActualLow.source F) q) = monomial F q := by
  have H := IntegralCriticalFlatGenericMonomialBits.actual_value_at F.toParameters (IntegralCriticalFlatActualLow.source F)
    (IntegralCriticalFlatActualLow.access F h) (answer F) q (coefficient_replies F h q) (height_replies F h q)
  exact H.trans (entryBits_fin (factorMatrix (IntegralCriticalFlatActualLow.source F) q
    (IntegralCriticalHistoryTask.get F.toParameters .slot8 q))
    (IntegralCriticalFlatGenericMonomialBits.index F.toParameters (IntegralCriticalFlatActualLow.source F) .row q)
    (IntegralCriticalFlatGenericMonomialBits.index F.toParameters (IntegralCriticalFlatActualLow.source F) .col q)).symm

end LeanCanny.Algebra.IntegralCriticalActualMonomialReplies

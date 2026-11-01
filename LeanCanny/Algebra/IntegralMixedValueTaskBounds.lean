/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueHomogeneousQueries
public import LeanCanny.Algebra.IntegralMixedVirtualCaps

/-! # Actual value Gram selectors fit the one original scalar cap

The initial exceptional degree ceiling bounds the whole spatial Gram
dimension, hence its columns and the smaller homogeneous row requests.
No absolute norm degree or later parameter-algebra rank enters this bound.
The root task cap already contains the retained scalar rank, which bounds
one nilpotent digit independently of the current physical prefix length.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueTaskBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualCaps IntegralMixedValueHomogeneousQueries
open scoped Classical

theorem scalar_le_root_cap (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool) :
    2 ^ F.width (IntegralMixedVirtualTaskBits.saved P q) ≤ numericCap P (RankedHistoryTask.root q) := by
  rw [h.width]
  apply le_trans _ (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.1
  change 2 ^ P.width (RankedHistoryTask.root q) ≤
    (2 ^ P.width (RankedHistoryTask.root q)) ^ (P.cap (RankedHistoryTask.root q) + 1)
  conv_lhs => rw [← pow_one (2 ^ P.width (RankedHistoryTask.root q))]
  exact Nat.pow_le_pow_right (Nat.two_pow_pos _) (by omega)

theorem dimension_lt_scalar (F : Family) (q : List Bool) :
    IntegralMixedGridValue.dimension (F.spatial q) (F.rule q) < 2 ^ F.width q :=
  (IntegralMixedValueDoubleNilpotent.dimension_lt (F.spatial q) (F.rule q)).trans_le (F.scalar_cap q)

theorem columns_lt_scalar (F : Family) (q : List Bool) :
    count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) < 2 ^ F.width q := by
  apply lt_of_le_of_lt _ (dimension_lt_scalar F q)
  change _ ≤ (F.ambient q - (F.rule q).critical.offset.val + 1 + 3) * _
  exact (Nat.one_mul _).symm.trans_le (Nat.mul_le_mul_right _ (by omega))

theorem coordinateDegree_lt_scalar (F : Family) (q : List Bool) :
    IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q) < 2 ^ F.width q := by
  have HK := IntegralMixedExceptionalBounds.coordinateCap_le (F.spatial q).degree (F.rule q)
  have HS := F.scalar_cap q
  unfold IntegralMixedExceptionalBounds.auxiliaryCap at HS
  change PurePowerReductionBounds.dimension (F.ambient q - (F.rule q).critical.offset.val + 1) (F.spatial q).degree < 2 ^ F.width q
  omega

theorem free_lt_scalar (F : Family) (q : List Bool) :
    F.ambient q - (F.rule q).critical.offset.val + 1 < 2 ^ F.width q := by
  have HC : 1 ≤ count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) := Nat.succ_le_of_lt (pow_pos (Nat.two_pow_pos _) _)
  have HM := Nat.mul_le_mul_left (F.ambient q - (F.rule q).critical.offset.val + 1 + 3) HC
  rw [Nat.mul_one] at HM
  have HD := dimension_lt_scalar F q
  change (F.ambient q - (F.rule q).critical.offset.val + 1 + 3) * _ < _ at HD
  omega

theorem originalTarget_lt_scalar (P : Parameters) (F : Family) (q : List Bool)
    (hr : HomogeneousSystemCoefficientRequest.request (parameters P F) (packet P q)) :
    originalTarget P F q < 2 ^ F.width (IntegralMixedVirtualTaskBits.saved P q) := by
  have HT := HomogeneousSystemCoefficientRequest.stripped_bound (parameters P F) (packet P q) hr
  have HC := columns_lt_scalar (IntegralMixedVirtualTaskBits.family P F) q
  have HM : count ((parameters P F).free q) ((parameters P F).width q) ≤
      count ((parameters P F).free q + 1) ((parameters P F).width q) :=
    Nat.pow_le_pow_right (Nat.two_pow_pos _) (Nat.le_succ _)
  have HX : MacaulayFullBoxBits.ctx (packet P q) = q := by
    simp only [packet, MacaulayFullBoxBits.entryPacket, MacaulayFullBoxBits.ctx, pairFst_pair]
  rw [HX] at HT
  exact (HT.trans_le HM).trans HC

theorem coordinate_bounds (P : Parameters) (F : Family) (q : List Bool)
    (hr : HomogeneousSystemCoefficientRequest.request (parameters P F) (packet P q))
    (hz : get P .slot8 q ≠ 0) :
    get P .slot8 q - 1 < 2 ^ F.width (IntegralMixedVirtualTaskBits.saved P q) ∧
      IntegralMixedValueHomogeneousQueries.coordinateCoefficient P F q < 2 ^ F.width (IntegralMixedVirtualTaskBits.saved P q) := by
  have HX : MacaulayFullBoxBits.ctx (packet P q) = q := by
    simp only [packet, MacaulayFullBoxBits.entryPacket, MacaulayFullBoxBits.ctx, pairFst_pair]
  have HJ : HomogeneousSystemCoefficientRequest.row (packet P q) = get P .slot8 q := by
    simp only [packet, HomogeneousSystemCoefficientRequest.row, IntegralReciprocalEntryRequest.row,
      MacaulayFullBoxBits.entryPacket, MacaulayFullBoxBits.idx, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HN : HomogeneousSystemCoefficientRequest.row (packet P q) ≠ 0 := HJ ▸ hz
  have HC := HomogeneousSystemCoefficientRequest.coordinate_lt (parameters P F) (packet P q) hr HN
  have HE := HomogeneousSystemCoefficientRequest.coefficient_le_coordinateDegree (parameters P F) (packet P q) hr HN
  rw [HX, HJ] at HC
  rw [HX] at HE
  exact ⟨HC.trans (free_lt_scalar (IntegralMixedVirtualTaskBits.family P F) q),
    HE.trans_lt (coordinateDegree_lt_scalar (IntegralMixedVirtualTaskBits.family P F) q)⟩

theorem originalTarget_cap (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool)
    (hr : HomogeneousSystemCoefficientRequest.request (parameters P F) (packet P q)) :
    originalTarget P F q ≤ numericCap P (RankedHistoryTask.root q) :=
  (originalTarget_lt_scalar P F q hr).le.trans (scalar_le_root_cap P F h q)

theorem coordinate_caps (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool)
    (hr : HomogeneousSystemCoefficientRequest.request (parameters P F) (packet P q))
    (hz : get P .slot8 q ≠ 0) :
    get P .slot8 q - 1 ≤ numericCap P (RankedHistoryTask.root q) ∧
      IntegralMixedValueHomogeneousQueries.coordinateCoefficient P F q ≤ numericCap P (RankedHistoryTask.root q) :=
  ⟨(coordinate_bounds P F q hr hz).1.le.trans (scalar_le_root_cap P F h q),
    (coordinate_bounds P F q hr hz).2.le.trans (scalar_le_root_cap P F h q)⟩

theorem coordinateTask_value_guarded (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool)
    (hr : HomogeneousSystemCoefficientRequest.request (parameters P F) (packet P q))
    (hz : get P .slot8 q ≠ 0) :
    (IntegralMixedVirtualTaskBits.source P F).value (coordinateTask P F q) =
      MatrixPower.residueBits (IntegralMixedVirtualQueryBits.matrixCoefficient F (IntegralMixedVirtualTaskBits.saved P q)
        (get P .slot8 q - 1) (IntegralMixedValueHomogeneousQueries.coordinateCoefficient P F q) (get P .row q) (get P .col q) : ZMod (modulus P q)) :=
  coordinateTask_value P F q (coordinate_caps P F h q hr hz).1 (coordinate_caps P F h q hr hz).2

end LeanCanny.Algebra.IntegralMixedValueTaskBounds

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationMomentMatrix
public import LeanCanny.Algebra.IntegralMixedNormalizationCharacteristic
/-! # Actual normalization augmented entries and finite power replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev moment (P : Parameters) (F : Family) := IntegralCriticalFlatMomentBits.source P (source P F)
noncomputable def momentEntry (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  IntegralMixedNormalizationMomentMatrixBits.modularEntry P F q
    (get P .row q % IntegralMixedNormalizationMomentMatrixBits.size P F q)
    (get P .col q % IntegralMixedNormalizationMomentMatrixBits.size P F q)

theorem moment_rank (P : Parameters) (F : Family) (q : List Bool) : (moment P F).rank q = (source P F).rank q := by
  change (source P F).rank (IntegralBerkowitzBlockBits.original (IntegralCriticalFlatMomentBits.packet P q)) = _
  rw [IntegralCriticalFlatMomentBits.packet_parent]

theorem moment_size_pos (P : Parameters) (F : Family) (q : List Bool) : 0 < IntegralMixedNormalizationMomentMatrixBits.size P F q := by
  have HR : 0 < (moment P F).rank q := (moment_rank P F q).symm ▸ (source P F).rank_pos q
  change 0 < ((moment P F).dimension q + 2) * (moment P F).rank q
  exact Nat.mul_pos (by omega) HR

theorem moment_modulus (P : Parameters) (F : Family) (q : List Bool) : (moment P F).modulus q = modulus P q := by
  change (source P F).modulus (IntegralBerkowitzBlockBits.original (IntegralCriticalFlatMomentBits.packet P q)) = _
  rw [IntegralCriticalFlatMomentBits.packet_parent]
  rfl

theorem moment_dimension_le (P : Parameters) (F : Family) (q : List Bool) : (moment P F).dimension q ≤ (source P F).dimension q := by
  change IntegralBerkowitzBlockBits.remaining (source P F) (IntegralCriticalFlatMomentBits.packet P q) ≤ _
  unfold IntegralBerkowitzBlockBits.remaining
  rw [IntegralCriticalFlatMomentBits.packet_parent]
  exact (Nat.sub_le _ _).trans (Nat.sub_le _ _)

theorem moment_size_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralMixedNormalizationMomentMatrixBits.size P F q ≤ numericCap P (RankedHistoryTask.root q) := by
  have HD := moment_dimension_le P F q
  have HR : (moment P F).rank q = 1 := moment_rank P F q
  have HC := augmented_cap P F g q hv
  change ((moment P F).dimension q + 2) * (moment P F).rank q ≤ _
  rw [HR]
  exact (Nat.mul_le_mul_right 1 (Nat.add_le_add_right HD 2)).trans HC

attribute [local irreducible] source access IntegralMixedNormalizationMomentMatrixBits.modularEntry
  IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

theorem moment_entry_child (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (i j : Fin (IntegralMixedNormalizationMomentMatrixBits.size P F q)) :
    momentEntry P F (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((moment P F).powerMatrix q i j : ℤ) : ZMod ((moment P F).modulus q)) := by
  let c := IntegralCriticalFlatMatrixQuery.writer P .monomialFactor
    (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HR : RankedHistoryTask.root c = RankedHistoryTask.root q := by simp only [c, IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair]
  have HB : birth P c = birth P q := by simp only [c, IntegralCriticalFlatMatrixQuery.writer_birth, pairFst_pair]
  have HM : modulus P c = modulus P q := by simp only [c, IntegralCriticalFlatMatrixQuery.writer_modulus, pairFst_pair]
  have HX : get P .slot15 c = get P .slot15 q := by simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, reduceCtorEq, ite_false]
  have HS : get P .slot11 c = get P .slot11 q := by simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, reduceCtorEq, ite_false]
  have HT : get P .slot12 c = get P .slot12 q := by simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, reduceCtorEq, ite_false]
  have HD := IntegralMixedNormalizationMomentMatrixBits.size_transport P F q c HR HB HX HS HT
  have HI : get P .row c = i.val := by
    simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]
    exact min_eq_left (i.isLt.le.trans (moment_size_cap P F g q hv))
  have HK : get P .col c = j.val := by
    simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, reduceCtorEq, ite_true, ite_false]
    exact min_eq_left (j.isLt.le.trans (moment_size_cap P F g q hv))
  change momentEntry P F c = _
  unfold momentEntry
  rw [HI, HK, HD, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt]
  have HE := (IntegralMixedNormalizationMomentMatrixBits.modularEntry_transport P F q c HR HB HX HS HT HM i.val j.val).trans
    (IntegralMixedNormalizationMomentMatrixBits.modularEntry_fin P F q i j)
  exact HE.trans (congrArg (fun m => residueBits (((moment P F).powerMatrix q i j : ℤ) : ZMod m)) (moment_modulus P F q).symm)

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits

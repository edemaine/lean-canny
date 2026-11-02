/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHeightIntegerModel
/-! # Native affine-height table arithmetic restores literal integer formulas -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHeightTableArithmeticBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedScalarCellsBits (cell)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] cell modulus IntegralMixedFramedHeightIntegerBits.bank BinaryNat.mulMod BinaryNat.powMod ArithmeticBits.combine

theorem bank_table (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedFramedHeightBankProductBits.value P (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) =
      residueBits (IntegralMixedFramedHeightIntegerBits.bank P D J q : ZMod (modulus P q)) := by
  unfold IntegralMixedFramedHeightIntegerBits.bank
  exact IntegralMixedFramedHeightBankProductBits.value_table P D J q

theorem scales_table (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedFramedHeightCellAccessBits.scaleProduct P D J (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) =
      residueBits (IntegralMixedFramedHeightIntegerBits.scales P D J q : ZMod (modulus P q)) := by
  have H := congrArg (fun c => residueBits (∏ i ∈ Finset.range (P.ambient (RankedHistoryTask.root c) + 1),
      if i = get P .slot8 c then (1 : ZMod (modulus P c)) else (cell P D J c 2 i : ZMod (modulus P c))))
    (pairFst_pair q (IntegralMixedFramedHeightTablePassBits.value P D J q))
  refine H.trans ?_
  unfold IntegralMixedFramedHeightIntegerBits.scales
  rw [Int.cast_prod]
  apply congrArg residueBits
  apply Finset.prod_congr rfl
  intro i _
  split_ifs
  · exact (Int.cast_one).symm
  · rfl

theorem power_table (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedFramedHeightScaleFactorBits.power P (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) =
      residueBits ((IntegralMixedFramedHeightIntegerBits.bank P D J q : ZMod (modulus P q)) ^ P.ambient (RankedHistoryTask.root q)) := by
  rw [IntegralMixedFramedHeightScaleFactorBits.power, bank_table P D J q]
  simp only [pairFst_pair]
  exact IntegralScaledCharacteristicBits.pow_residue _ _ (modulus_ne_zero P q) _

theorem factor_table (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedFramedHeightScaleFactorBits.factor P D J (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) =
      residueBits (IntegralMixedFramedHeightIntegerBits.factor P D J q : ZMod (modulus P q)) := by
  rw [IntegralMixedFramedHeightScaleFactorBits.factor, power_table P D J q, scales_table P D J q]
  simp only [IntegralMixedFramedHeightReferenceSumBits.multiply, pairFst_pair, pairSnd_pair]
  simpa only [IntegralMixedFramedHeightIntegerBits.factor, Int.cast_mul, Int.cast_pow] using ArithmeticBits.mulMod_residueBits (modulus P q)
    ((IntegralMixedFramedHeightIntegerBits.bank P D J q : ZMod (modulus P q)) ^ P.ambient (RankedHistoryTask.root q))
    (IntegralMixedFramedHeightIntegerBits.scales P D J q : ZMod (modulus P q))

theorem references_table (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedFramedHeightReferenceSumBits.value P D J (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) =
      residueBits (IntegralMixedFramedHeightIntegerBits.references P D J q : ZMod (modulus P q)) := by
  have H := congrArg (fun c => residueBits (∑ i ∈ Finset.range (birth P c),
      (cell P D J c 1 i : ZMod (modulus P c)) * (IntegralMixedFramedHeightTableReadBits.number P
        (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) (birth P c + i) : ZMod (modulus P c))))
    (pairFst_pair q (IntegralMixedFramedHeightTablePassBits.value P D J q))
  refine H.trans ?_
  unfold IntegralMixedFramedHeightIntegerBits.references
  rw [Int.cast_sum]
  apply congrArg residueBits
  apply Finset.sum_congr rfl
  intro i hi
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  rw [IntegralMixedFramedHeightTableMatrixBits.number_height P D J q i (Finset.mem_range.mp hi), ZMod.natCast_zmod_val, Int.cast_mul]

theorem coefficient_packet (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (tag : ℕ) (q table : List Bool) :
    IntegralMixedFramedHeightAffineSumBits.coefficient P D J tag (pair q table) = residueBits (cell P D J q tag 0 : ZMod (modulus P q)) := by
  simp only [IntegralMixedFramedHeightAffineSumBits.coefficient, IntegralMixedFramedHeightCellAccessBits.read, Function.comp_apply,
    IntegralMixedFramedHeightCellAccessBits.query, pairFst_pair, pairSnd_pair]
  exact IntegralMixedFramedScalarCellsBits.reader_packet P D J q tag 0

theorem diagonal_table (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedFramedHeightAffineSumBits.diagonalConstant P D J (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) =
      residueBits (IntegralMixedFramedHeightIntegerBits.constant P D J q : ZMod (modulus P q)) := by
  unfold IntegralMixedFramedHeightAffineSumBits.diagonalConstant IntegralMixedFramedHeightAffineSumBits.diagonal
  simp only [pairFst_pair]
  by_cases HD : IntegralMixedHeightTableQueryBits.oldRow P q = IntegralMixedHeightTableQueryBits.oldCol P q
  · rw [ite_eq_left HD, coefficient_packet]
    simp only [IntegralMixedFramedHeightIntegerBits.constant, ite_eq_left HD]
  · rw [ite_eq_right HD]
    simp only [IntegralMixedFramedHeightIntegerBits.constant, ite_eq_right HD, Int.cast_zero]
    exact ArithmeticBits.zero_residueBits _

theorem affine_table (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedFramedHeightAffineSumBits.value P D J (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) =
      residueBits (IntegralMixedFramedHeightIntegerBits.affine P D J q : ZMod (modulus P q)) := by
  rw [IntegralMixedFramedHeightAffineSumBits.value, references_table P D J q, bank_table P D J q, diagonal_table P D J q]
  simp only [IntegralMixedFramedHeightAffineSumBits.finish, pairFst_pair, pairSnd_pair]
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  simpa only [IntegralMixedFramedHeightIntegerBits.affine, Int.cast_add, Int.cast_mul] using
    ArithmeticBits.combine_residueBits (modulus P q) (IntegralMixedFramedHeightIntegerBits.references P D J q : ZMod (modulus P q))
      (IntegralMixedFramedHeightIntegerBits.bank P D J q : ZMod (modulus P q)) (IntegralMixedFramedHeightIntegerBits.constant P D J q : ZMod (modulus P q))

theorem constant_table (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedFramedHeightPostBits.constantValue P D J (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) =
      residueBits (IntegralMixedFramedHeightIntegerBits.factor P D J q * IntegralMixedFramedHeightIntegerBits.affine P D J q : ZMod (modulus P q)) := by
  rw [IntegralMixedFramedHeightPostBits.constantValue, factor_table P D J q, affine_table P D J q]
  simp only [IntegralMixedFramedHeightReferenceSumBits.multiply, pairFst_pair, pairSnd_pair]
  exact ArithmeticBits.mulMod_residueBits _ _ _

theorem slope_table (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedFramedHeightPostBits.slopeValue P D J (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) =
      residueBits (IntegralMixedFramedHeightIntegerBits.factor P D J q * cell P D J q 3 0 : ZMod (modulus P q)) := by
  rw [IntegralMixedFramedHeightPostBits.slopeValue, factor_table P D J q, coefficient_packet]
  simp only [IntegralMixedFramedHeightReferenceSumBits.multiply, pairFst_pair, pairSnd_pair]
  exact ArithmeticBits.mulMod_residueBits _ _ _

theorem post_table (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedFramedHeightPostBits.post P D J (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) = IntegralMixedFramedHeightIntegerBits.word P D J q := by
  unfold IntegralMixedFramedHeightPostBits.post IntegralMixedFramedHeightIntegerBits.word IntegralMixedFramedHeightIntegerBits.value
  simp only [IntegralMixedFramedHeightPostBits.guard, IntegralMixedFramedHeightPostBits.constantBranch, IntegralMixedFramedHeightPostBits.slopeBranch,
    IntegralMixedFramedHeightAffineSumBits.diagonal, pairFst_pair]
  split_ifs
  · rw [constant_table, Int.cast_mul]
  · rw [slope_table, Int.cast_mul]
  all_goals rw [Int.cast_zero]
  all_goals exact ArithmeticBits.zero_residueBits _

end LeanCanny.Algebra.IntegralMixedFramedHeightTableArithmeticBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightIntegerModel
/-! # Native affine-height table arithmetic restores literal integer formulas -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightTableArithmeticBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHeightCellsBits (cell)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] cell modulus IntegralMixedHeightIntegerBits.bank BinaryNat.mulMod BinaryNat.powMod ArithmeticBits.combine

theorem bank_table (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    IntegralMixedHeightBankProductBits.value P (pair q (IntegralMixedHeightTablePassBits.value P D q)) =
      residueBits (IntegralMixedHeightIntegerBits.bank P D q : ZMod (modulus P q)) := by
  unfold IntegralMixedHeightIntegerBits.bank
  exact IntegralMixedHeightBankProductBits.value_table P D q

theorem scales_table (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    IntegralMixedHeightCellAccessBits.scaleProduct P D (pair q (IntegralMixedHeightTablePassBits.value P D q)) =
      residueBits (IntegralMixedHeightIntegerBits.scales P D q : ZMod (modulus P q)) := by
  have H := congrArg (fun c => residueBits (∏ i ∈ Finset.range (P.ambient (RankedHistoryTask.root c) + 1),
      if i = get P .slot8 c then (1 : ZMod (modulus P c)) else (cell P D c 2 i : ZMod (modulus P c))))
    (pairFst_pair q (IntegralMixedHeightTablePassBits.value P D q))
  refine H.trans ?_
  unfold IntegralMixedHeightIntegerBits.scales
  rw [Int.cast_prod]
  apply congrArg residueBits
  apply Finset.prod_congr rfl
  intro i _
  split_ifs
  · exact (Int.cast_one).symm
  · rfl

theorem power_table (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    IntegralMixedHeightScaleFactorBits.power P (pair q (IntegralMixedHeightTablePassBits.value P D q)) =
      residueBits ((IntegralMixedHeightIntegerBits.bank P D q : ZMod (modulus P q)) ^ P.ambient (RankedHistoryTask.root q)) := by
  rw [IntegralMixedHeightScaleFactorBits.power, bank_table P D q]
  simp only [pairFst_pair]
  exact IntegralScaledCharacteristicBits.pow_residue _ _ (modulus_ne_zero P q) _

theorem factor_table (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    IntegralMixedHeightScaleFactorBits.factor P D (pair q (IntegralMixedHeightTablePassBits.value P D q)) =
      residueBits (IntegralMixedHeightIntegerBits.factor P D q : ZMod (modulus P q)) := by
  rw [IntegralMixedHeightScaleFactorBits.factor, power_table P D q, scales_table P D q]
  simp only [IntegralMixedHeightReferenceSumBits.multiply, pairFst_pair, pairSnd_pair]
  simpa only [IntegralMixedHeightIntegerBits.factor, Int.cast_mul, Int.cast_pow] using ArithmeticBits.mulMod_residueBits (modulus P q)
    ((IntegralMixedHeightIntegerBits.bank P D q : ZMod (modulus P q)) ^ P.ambient (RankedHistoryTask.root q))
    (IntegralMixedHeightIntegerBits.scales P D q : ZMod (modulus P q))

theorem references_table (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    IntegralMixedHeightReferenceSumBits.value P D (pair q (IntegralMixedHeightTablePassBits.value P D q)) =
      residueBits (IntegralMixedHeightIntegerBits.references P D q : ZMod (modulus P q)) := by
  have H := congrArg (fun c => residueBits (∑ i ∈ Finset.range (birth P c),
      (cell P D c 1 i : ZMod (modulus P c)) * (IntegralMixedHeightTableReadBits.number P
        (pair q (IntegralMixedHeightTablePassBits.value P D q)) (birth P c + i) : ZMod (modulus P c))))
    (pairFst_pair q (IntegralMixedHeightTablePassBits.value P D q))
  refine H.trans ?_
  unfold IntegralMixedHeightIntegerBits.references
  rw [Int.cast_sum]
  apply congrArg residueBits
  apply Finset.sum_congr rfl
  intro i hi
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  rw [IntegralMixedHeightTableMatrixBits.number_height P D q i (Finset.mem_range.mp hi), ZMod.natCast_zmod_val, Int.cast_mul]

theorem coefficient_packet (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (tag : ℕ) (q table : List Bool) :
    IntegralMixedHeightAffineSumBits.coefficient P D tag (pair q table) = residueBits (cell P D q tag 0 : ZMod (modulus P q)) := by
  simp only [IntegralMixedHeightAffineSumBits.coefficient, IntegralMixedHeightCellAccessBits.read, Function.comp_apply,
    IntegralMixedHeightCellAccessBits.query, pairFst_pair, pairSnd_pair]
  exact IntegralMixedHeightCellsBits.reader_packet P D q tag 0

theorem diagonal_table (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    IntegralMixedHeightAffineSumBits.diagonalConstant P D (pair q (IntegralMixedHeightTablePassBits.value P D q)) =
      residueBits (IntegralMixedHeightIntegerBits.constant P D q : ZMod (modulus P q)) := by
  unfold IntegralMixedHeightAffineSumBits.diagonalConstant IntegralMixedHeightAffineSumBits.diagonal
  simp only [pairFst_pair]
  by_cases HD : IntegralMixedHeightTableQueryBits.oldRow P q = IntegralMixedHeightTableQueryBits.oldCol P q
  · rw [ite_eq_left HD, coefficient_packet]
    simp only [IntegralMixedHeightIntegerBits.constant, ite_eq_left HD]
  · rw [ite_eq_right HD]
    simp only [IntegralMixedHeightIntegerBits.constant, ite_eq_right HD, Int.cast_zero]
    exact ArithmeticBits.zero_residueBits _

theorem affine_table (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    IntegralMixedHeightAffineSumBits.value P D (pair q (IntegralMixedHeightTablePassBits.value P D q)) =
      residueBits (IntegralMixedHeightIntegerBits.affine P D q : ZMod (modulus P q)) := by
  rw [IntegralMixedHeightAffineSumBits.value, references_table P D q, bank_table P D q, diagonal_table P D q]
  simp only [IntegralMixedHeightAffineSumBits.finish, pairFst_pair, pairSnd_pair]
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  simpa only [IntegralMixedHeightIntegerBits.affine, Int.cast_add, Int.cast_mul] using
    ArithmeticBits.combine_residueBits (modulus P q) (IntegralMixedHeightIntegerBits.references P D q : ZMod (modulus P q))
      (IntegralMixedHeightIntegerBits.bank P D q : ZMod (modulus P q)) (IntegralMixedHeightIntegerBits.constant P D q : ZMod (modulus P q))

theorem constant_table (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    IntegralMixedHeightPostBits.constantValue P D (pair q (IntegralMixedHeightTablePassBits.value P D q)) =
      residueBits (IntegralMixedHeightIntegerBits.factor P D q * IntegralMixedHeightIntegerBits.affine P D q : ZMod (modulus P q)) := by
  rw [IntegralMixedHeightPostBits.constantValue, factor_table P D q, affine_table P D q]
  simp only [IntegralMixedHeightReferenceSumBits.multiply, pairFst_pair, pairSnd_pair]
  exact ArithmeticBits.mulMod_residueBits _ _ _

theorem slope_table (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    IntegralMixedHeightPostBits.slopeValue P D (pair q (IntegralMixedHeightTablePassBits.value P D q)) =
      residueBits (IntegralMixedHeightIntegerBits.factor P D q * cell P D q 3 0 : ZMod (modulus P q)) := by
  rw [IntegralMixedHeightPostBits.slopeValue, factor_table P D q, coefficient_packet]
  simp only [IntegralMixedHeightReferenceSumBits.multiply, pairFst_pair, pairSnd_pair]
  exact ArithmeticBits.mulMod_residueBits _ _ _

theorem post_table (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    IntegralMixedHeightPostBits.post P D (pair q (IntegralMixedHeightTablePassBits.value P D q)) = IntegralMixedHeightIntegerBits.word P D q := by
  unfold IntegralMixedHeightPostBits.post IntegralMixedHeightIntegerBits.word IntegralMixedHeightIntegerBits.value
  simp only [IntegralMixedHeightPostBits.guard, IntegralMixedHeightPostBits.constantBranch, IntegralMixedHeightPostBits.slopeBranch,
    IntegralMixedHeightAffineSumBits.diagonal, pairFst_pair]
  split_ifs
  · rw [constant_table, Int.cast_mul]
  · rw [slope_table, Int.cast_mul]
  all_goals rw [Int.cast_zero]
  all_goals exact ArithmeticBits.zero_residueBits _

end LeanCanny.Algebra.IntegralMixedHeightTableArithmeticBits

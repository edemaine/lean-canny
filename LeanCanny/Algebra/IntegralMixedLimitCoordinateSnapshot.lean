/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateRoot
public import LeanCanny.Algebra.IntegralMixedCoordinateCoefficientSnapshot
/-! # Actual limit-coordinate coefficients from old coordinate matrix entries

The exponent uses the fixed original spatial dimension allowance. The only
old coefficient is a literal coordinate-factor coefficient at indices k,c-k.
Natural matrix indices retain the total zero convention outside the rank.
No new cut constructor or interpreted-history reader is introduced here.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitCoordinateSnapshot
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedCutSource
open scoped Classical
attribute [local irreducible] IntegralMixedCriticalSweep.coordinate

noncomputable def coordinate (F : Family) (key : List Bool) (j : ℕ) :=
  IntegralMixedCoordinateCoefficientSnapshot.coordinate F key j

noncomputable def choice (F : Family) (key : List Bool) (c : ℕ) :
    Fin (IntegralMixedLimitCoordinate.ChoiceBound (F.spatial key) (F.rule key)) :=
  IntegralMixedCoordinateCoefficientSnapshot.choice F key c

noncomputable def factor (F : Family) (key : List Bool) (j c : ℕ) :=
  IntegralMixedLimitCoordinate.factor (F.state key) (F.birth_bound key) (F.rule key)
    (coordinate F key j) (choice F key c)

def degree (F : Family) (key : List Bool) : ℕ :=
  IntegralMixedLimitCoordinate.degree (F.spatial key) (F.rule key)

noncomputable def denominator (F : Family) (key : List Bool) : ℤ := IntegralMixedHistory.commonDenominator (F.state key)

noncomputable def matrix (F : Family) (key : List Bool) (j c k : ℕ) :
    Matrix (Fin (count (F.birth key) (F.width key))) (Fin (count (F.birth key) (F.width key))) ℤ :=
  Algebra.leftMulMatrix (F.state key).sampler.scalarPrefix.basis.finBasis ((factor F key j c).coeff k)

noncomputable def coefficient (F : Family) (key : List Bool) (j c k r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry (matrix F key j c k) r t

theorem coordinate_fin (F : Family) (key : List Bool)
    (j : Fin (F.ambient key - (F.rule key).critical.offset.val + 1)) : coordinate F key j.val = j :=
  Fin.ext (Nat.mod_eq_of_lt j.isLt)

theorem choice_fin (F : Family) (key : List Bool)
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (F.spatial key) (F.rule key))) : choice F key c.val = c :=
  Fin.ext (Nat.mod_eq_of_lt c.isLt)

theorem factor_fin (F : Family) (key : List Bool)
    (j : Fin (F.ambient key - (F.rule key).critical.offset.val + 1))
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (F.spatial key) (F.rule key))) :
    factor F key j.val c.val = IntegralMixedLimitCoordinate.factor (F.state key) (F.birth_bound key) (F.rule key) j c := by
  unfold factor
  rw [coordinate_fin, choice_fin]

theorem degree_eq (F : Family) (key : List Bool) : degree F key =
    PurePowerReductionBounds.dimension (F.ambient key - (F.rule key).critical.offset.val + 1) (F.spatial key).degree := rfl

theorem choice_value (F : Family) (key : List Bool) (c : ℕ)
    (hc : c < IntegralMixedLimitCoordinate.ChoiceBound (F.spatial key) (F.rule key)) :
    (choice F key c).val = c := Nat.mod_eq_of_lt hc

theorem old_choice_bound (F : Family) (key : List Bool) (c k : ℕ)
    (hc : c < IntegralMixedLimitCoordinate.ChoiceBound (F.spatial key) (F.rule key)) (hk : k ≤ c) :
    k < IntegralMixedCoordinateTrailing.ChoiceBound (F.spatial key) (F.rule key) := hk.trans_lt hc

theorem matrix_eq (F : Family) (key : List Bool) (j c k : ℕ)
    (hc : c < IntegralMixedLimitCoordinate.ChoiceBound (F.spatial key) (F.rule key)) :
    matrix F key j c k = if k ≤ c then denominator F key ^ (degree F key-k) •
      Algebra.leftMulMatrix (F.state key).sampler.scalarPrefix.basis.finBasis
        (((IntegralMixedCriticalSweep.coordinate (F.state key) (F.birth_bound key) (F.rule key)
          (coordinate F key j)).coeff k).coeff (c-k)) else 0 := by
  unfold matrix factor
  rw [IntegralMixedLimitCoordinate.factor_coefficient, choice_value F key c hc]
  split_ifs
  · rw [← Int.cast_pow, mul_comm, ← zsmul_eq_mul]
    exact map_zsmul (Algebra.leftMulMatrix _) _ _
  · exact map_zero _

theorem old_coefficient (F : Family) (key : List Bool) (j k l r t : ℕ)
    (hk : k < IntegralMixedCoordinateTrailing.ChoiceBound (F.spatial key) (F.rule key)) :
    IntegralCriticalTotalSnapshotBits.integerEntry
      (Algebra.leftMulMatrix (F.state key).sampler.scalarPrefix.basis.finBasis
        (((IntegralMixedCriticalSweep.coordinate (F.state key) (F.birth_bound key) (F.rule key)
          (coordinate F key j)).coeff k).coeff l)) r t =
      IntegralMixedCoordinateCoefficientSnapshot.coefficient F key j k l r t := by
  unfold IntegralMixedCoordinateCoefficientSnapshot.coefficient IntegralMixedCutMatrix.coefficientMatrix
    IntegralMixedCoordinateCoefficientSnapshot.kind IntegralMixedRelativeCuts.factor IntegralMixedCoordinateTrailing.factor
  simp only [IntegralMixedCoordinateCoefficientSnapshot.choice, Nat.mod_eq_of_lt hk]
  rfl

theorem integerEntry_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (z : ℤ) (r t : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry (z • M) r t =
      z * IntegralCriticalTotalSnapshotBits.integerEntry M r t := by
  unfold IntegralCriticalTotalSnapshotBits.integerEntry
  split_ifs <;> simp [Matrix.smul_apply]

theorem coefficient_eq (F : Family) (key : List Bool) (j c k r t : ℕ)
    (hc : c < IntegralMixedLimitCoordinate.ChoiceBound (F.spatial key) (F.rule key)) :
    coefficient F key j c k r t = if k ≤ c then denominator F key ^ (degree F key-k) *
      IntegralMixedCoordinateCoefficientSnapshot.coefficient F key j k (c-k) r t else 0 := by
  unfold coefficient
  rw [matrix_eq F key j c k hc]
  by_cases hk : k ≤ c
  · rw [ite_eq_left hk, ite_eq_left hk, integerEntry_smul,
      old_coefficient F key j k (c-k) r t (old_choice_bound F key c k hc hk)]
  · rw [ite_eq_right hk, ite_eq_right hk]
    simp only [IntegralCriticalTotalSnapshotBits.integerEntry, Matrix.zero_apply, dite_eq_ite, ite_self]

theorem coefficient_zero (F : Family) (key : List Bool) (j c k r t : ℕ)
    (hc : c < IntegralMixedLimitCoordinate.ChoiceBound (F.spatial key) (F.rule key)) (hk : c < k) :
    coefficient F key j c k r t = 0 := by
  rw [coefficient_eq F key j c k r t hc, ite_eq_right (by omega : ¬k ≤ c)]

theorem coefficient_invalid_row (F : Family) (key : List Bool) (j c k r t : ℕ)
    (hr : count (F.birth key) (F.width key) ≤ r) : coefficient F key j c k r t = 0 := by
  unfold coefficient IntegralCriticalTotalSnapshotBits.integerEntry
  rw [dite_eq_right (by omega : ¬r < count (F.birth key) (F.width key))]

theorem coefficient_invalid_col (F : Family) (key : List Bool) (j c k r t : ℕ)
    (ht : count (F.birth key) (F.width key) ≤ t) : coefficient F key j c k r t = 0 := by
  unfold coefficient IntegralCriticalTotalSnapshotBits.integerEntry
  by_cases hr : r < count (F.birth key) (F.width key)
  · rw [dite_eq_left hr, dite_eq_right (by omega : ¬t < count (F.birth key) (F.width key))]
  · rw [dite_eq_right hr]

end LeanCanny.Algebra.IntegralMixedLimitCoordinateSnapshot

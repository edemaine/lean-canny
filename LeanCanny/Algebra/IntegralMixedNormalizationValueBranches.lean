/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeProductSum
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeLeading
/-! # The literal normalized coefficient agrees with its three native branches -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.modulus

theorem integerZeroBits (m : ℕ) : residueBits ((0 : ℤ) : ZMod m) = [] := by
  simpa only [Int.cast_zero, ArithmeticBits.zero] using (ArithmeticBits.zero_residueBits m).symm

theorem integerEntry_zero (n r t : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry (0 : Matrix (Fin n) (Fin n) ℤ) r t = 0 := by
  unfold IntegralCriticalTotalSnapshotBits.integerEntry
  split_ifs <;> rfl

theorem integerEntry_scalar {n : ℕ} (a : ℤ) (r t : ℕ) (hr : r < n) (ht : t < n) :
    IntegralCriticalTotalSnapshotBits.integerEntry (a • (1 : Matrix (Fin n) (Fin n) ℤ)) r t = if r = t then a else 0 := by
  unfold IntegralCriticalTotalSnapshotBits.integerEntry
  rw [dite_eq_left hr, dite_eq_left ht]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Fin.mk.injEq]
  by_cases HE : r = t <;> simp only [HE, ite_true, ite_false, mul_one, mul_zero]

attribute [local irreducible] IntegralMixedCutNormalizedSource.matrix inverseMatrix rawCoefficient top

theorem normalizedValue_outside (P : Parameters) (F : Family) (q : List Bool) (ha : ¬ matrixAxes P F q) :
    normalizedValue P F q = [] := by
  unfold normalizedValue IntegralCriticalTotalSnapshotBits.integerEntry
  split_ifs with hr ht
  · exact False.elim (ha ⟨hr, ht⟩)
  · exact integerZeroBits (modulus P q)
  · exact integerZeroBits (modulus P q)

theorem normalizedValue_low (P : Parameters) (F : Family) (q : List Bool)
    (hk : get P .coefficient q < F.degree (IntegralMixedVirtualTaskBits.saved P q)) :
    normalizedValue P F q = productValue P F q := by
  unfold normalizedValue productValue
  rw [normalized_matrix_split, ite_eq_right (Nat.ne_of_lt hk), ite_eq_left hk.le]

theorem normalizedValue_above (P : Parameters) (F : Family) (q : List Bool)
    (hk : F.degree (IntegralMixedVirtualTaskBits.saved P q) < get P .coefficient q) :
    normalizedValue P F q = [] := by
  unfold normalizedValue
  rw [normalized_matrix_split, ite_eq_right (Nat.ne_of_gt hk), ite_eq_right (Nat.not_le.mpr hk), integerEntry_zero]
  exact integerZeroBits (modulus P q)

theorem normalizedValue_top (P : Parameters) (F : Family) (q : List Bool) (ha : matrixAxes P F q)
    (hk : get P .coefficient q = F.degree (IntegralMixedVirtualTaskBits.saved P q)) :
    normalizedValue P F q = if get P .row q = get P .col q then leadingValue P F q else [] := by
  unfold normalizedValue
  rw [normalized_matrix_split, ite_eq_left hk, integerEntry_scalar _ _ _ ha.1 ha.2]
  by_cases HE : get P .row q = get P .col q
  · rw [ite_eq_left HE, ite_eq_left HE]
    rfl
  · rw [ite_eq_right HE, ite_eq_right HE]
    exact integerZeroBits (modulus P q)

theorem productValue_next (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    productValue P F (IntegralCriticalFlatEulerBits.next P p q) = productValue P F q := by
  unfold productValue
  rw [saved_next, IntegralCriticalFlatEulerBits.next_get, IntegralCriticalFlatEulerBits.next_get,
    IntegralCriticalFlatEulerBits.next_get, IntegralCriticalFlatEulerBits.next_modulus]

theorem matrixAxes_next (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    matrixAxes P F (IntegralCriticalFlatEulerBits.next P p q) ↔ matrixAxes P F q := by
  have HD : matrixDimension P F (IntegralCriticalFlatEulerBits.next P p q) = matrixDimension P F q :=
    congrArg (dimension F) (saved_next P p q)
  unfold matrixAxes
  rw [HD, IntegralCriticalFlatEulerBits.next_get, IntegralCriticalFlatEulerBits.next_get]

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits

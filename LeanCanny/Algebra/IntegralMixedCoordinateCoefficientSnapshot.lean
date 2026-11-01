/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueCoefficientSnapshot
public import LeanCanny.Algebra.IntegralMixedHeightNaturalEntries
/-! # Coordinate raw coefficients are reflected entries of the actual critical polynomial -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCoordinateCoefficientSnapshot
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralCoordinateBasis
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def coordinate (F : Family) (key : List Bool) (j : ℕ) :
    Fin (F.ambient key - (F.rule key).critical.offset.val + 1) := ⟨j % _, Nat.mod_lt _ (Nat.succ_pos _)⟩
noncomputable def choice (F : Family) (key : List Bool) (c : ℕ) :
    Fin (IntegralMixedCoordinateTrailing.ChoiceBound (F.spatial key) (F.rule key)) :=
  ⟨c % _, Nat.mod_lt _ (Nat.succ_pos _)⟩
noncomputable def kind (F : Family) (key : List Bool) (j c : ℕ) :=
  IntegralMixedRelativeCuts.Kind.coordinate (coordinate F key j) (choice F key c)
noncomputable def first (F : Family) (key : List Bool) (j c r t : ℕ) : ℤ :=
  Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state key)).finBasis
    (IntegralMixedCutNilpotent.value (F.state key) (F.birth_bound key) (F.rule key) (kind F key j c))
    (IntegralMixedHeightNaturalEntries.index (F.birth key + 1) (F.width key) r)
    (IntegralMixedHeightNaturalEntries.index (F.birth key + 1) (F.width key) t)
noncomputable def coefficient (F : Family) (key : List Bool) (j c k r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry
    (IntegralMixedCutMatrix.coefficientMatrix (F.state key) (F.birth_bound key) (F.rule key) (kind F key j c) k) r t

theorem virtual_first (F : Family) (key : List Bool) (j c r t : ℕ)
    (hc : c < IntegralMixedCoordinateTrailing.ChoiceBound (F.spatial key) (F.rule key)) :
    IntegralMixedVirtualQueryBits.matrixCoefficient F key j c r t = first F key j c r t := by
  unfold IntegralMixedVirtualQueryBits.matrixCoefficient first kind IntegralMixedCutNilpotent.value
    IntegralMixedRelativeCuts.factor IntegralMixedCoordinateTrailing.factor
  simp only [choice, Nat.mod_eq_of_lt hc]
  rfl

theorem first_coefficient (F : Family) (key : List Bool) (j c : ℕ)
    (i t : Fin (count (F.birth key) (F.width key))) (k : Fin (2 ^ F.width key)) :
    first F key j c (k.val + 2 ^ F.width key * i.val) (2 ^ F.width key * t.val) =
      coefficient F key j c k.val i.val t.val := by
  let r := pairIndex (F.birth key) (F.width key) (i, k)
  let s := pairIndex (F.birth key) (F.width key) (t, 0)
  have hi : IntegralMixedHeightNaturalEntries.index (F.birth key + 1) (F.width key) r.val = r :=
    Fin.ext (Nat.mod_eq_of_lt r.isLt)
  have ht : IntegralMixedHeightNaturalEntries.index (F.birth key + 1) (F.width key) s.val = s :=
    Fin.ext (Nat.mod_eq_of_lt s.isLt)
  have he : first F key j c r.val s.val =
      IntegralMixedCutMatrix.coefficientMatrix (F.state key) (F.birth_bound key) (F.rule key) (kind F key j c) k.val i t := by
    unfold first
    rw [hi, ht]
    exact IntegralMixedCutNilpotent.coefficient (F.state key) (F.birth_bound key) (F.rule key)
      (kind F key j c) (F.scalar_cap key) k i t
  have hb := IntegralCriticalTotalSnapshotBits.integerEntry_fin
    (IntegralMixedCutMatrix.coefficientMatrix (F.state key) (F.birth_bound key) (F.rule key) (kind F key j c) k.val) i t
  simpa only [r, s, IntegralMixedCutNilpotent.pairIndex_value, Fin.val_zero, Nat.zero_add, coefficient] using he.trans hb.symm

theorem coefficient_zero (F : Family) (key : List Bool) (j c k r t : ℕ)
    (hk : 2 ^ F.width key ≤ k) : coefficient F key j c k r t = 0 := by
  have hz := IntegralMixedCutNilpotent.coefficient_outside (F.state key) (F.birth_bound key)
    (F.rule key) (kind F key j c) (F.scalar_cap key) k hk
  unfold coefficient
  rw [hz]
  simp only [IntegralCriticalTotalSnapshotBits.integerEntry, Matrix.zero_apply, dite_eq_ite, ite_self]

end LeanCanny.Algebra.IntegralMixedCoordinateCoefficientSnapshot

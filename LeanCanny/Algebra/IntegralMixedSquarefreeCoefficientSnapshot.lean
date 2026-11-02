/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSquarefreeFactorValue
public import LeanCanny.Algebra.IntegralMixedPscEntrySnapshot
public import LeanCanny.Algebra.IntegralMixedCoordinateCoefficientSnapshot
public import LeanCanny.Algebra.IntegralMixedHeightNaturalEntries
/-! # Squarefree coefficients are reflected entries of the actual PSC product -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSquarefreeCoefficientSnapshot
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralCoordinateBasis
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def coordinate (F : Family) (key : List Bool) (j : ℕ) :=
  IntegralMixedCoordinateCoefficientSnapshot.coordinate F key j
noncomputable def choice (F : Family) (key : List Bool) (c : ℕ) :=
  IntegralMixedPscEntrySnapshot.index F c key
noncomputable def kind (F : Family) (key : List Bool) (j c : ℕ) :=
  IntegralMixedRelativeCuts.Kind.squarefree (coordinate F key j) (choice F key c)
noncomputable def first (F : Family) (key : List Bool) (j c r t : ℕ) : ℤ :=
  Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state key)).finBasis
    (IntegralMixedCutNilpotent.value (F.state key) (F.birth_bound key) (F.rule key) (kind F key j c))
    (IntegralMixedHeightNaturalEntries.index (F.birth key + 1) (F.width key) r)
    (IntegralMixedHeightNaturalEntries.index (F.birth key + 1) (F.width key) t)
noncomputable def coefficient (F : Family) (key : List Bool) (j c k r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry
    (IntegralMixedCutMatrix.coefficientMatrix (F.state key) (F.birth_bound key) (F.rule key) (kind F key j c) k) r t

theorem factor_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedSquarefreeFactorBits.value P F q = residueBits
      (first F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q)
        (get P .row q) (get P .col q) : ZMod (modulus P q)) := rfl

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

end LeanCanny.Algebra.IntegralMixedSquarefreeCoefficientSnapshot

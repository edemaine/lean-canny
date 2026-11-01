/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalTotalMatrixSnapshot

/-! # Natural block labels decode to spatial and integral-basis labels

Both sides return zero outside the finite block matrix. This preserves
invalid labels rather than reducing them modulo the matrix dimension.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralNaturalBlockEntry
open IntegralCriticalTotalSnapshotBits
open scoped Classical

noncomputable def table {A : Type*} [CommRing A] {L M : ℕ}
    (basis : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin L) A) (i j r t : ℕ) : ℤ :=
  integerEntry (fun a b => integerEntry (Algebra.leftMulMatrix basis (T a b)) r t) i j

theorem table_finite {A : Type*} [CommRing A] {L M : ℕ}
    (basis : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin L) A)
    (i j : Fin L) (r t : Fin M) : table basis T i.val j.val r.val t.val = Algebra.leftMulMatrix basis (T i j) r t :=
  (integerEntry_fin (show Matrix (Fin L) (Fin L) ℤ from fun a b =>
    integerEntry (Algebra.leftMulMatrix basis (T a b)) r.val t.val) i j).trans
      (integerEntry_fin (Algebra.leftMulMatrix basis (T i j)) r t)

theorem entry_finite {A : Type*} [CommRing A] {L M : ℕ}
    (basis : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin L) A) (a b : Fin (L * M)) :
    integerEntry (IntegralCoefficientBlocks.blockHom basis L T) a.val b.val =
      table basis T a.divNat.val b.divNat.val a.modNat.val b.modNat.val := by
  rw [integerEntry_fin]
  have HA : finProdFinEquiv (a.divNat, a.modNat) = a := finProdFinEquiv.apply_symm_apply a
  have HB : finProdFinEquiv (b.divNat, b.modNat) = b := finProdFinEquiv.apply_symm_apply b
  have H := IntegralCoefficientBlocks.block_entry basis T a.divNat b.divNat a.modNat b.modNat
  rw [HA, HB] at H
  exact H.trans (table_finite basis T _ _ _ _).symm

theorem entry_all {A : Type*} [CommRing A] {L M : ℕ}
    (basis : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin L) A) (hm : 0 < M) (a b : ℕ) :
    integerEntry (IntegralCoefficientBlocks.blockHom basis L T) a b =
      table basis T (a / M) (b / M) (a % M) (b % M) := by
  by_cases HA : a < L * M
  · by_cases HB : b < L * M
    · exact entry_finite basis T ⟨a, HA⟩ ⟨b, HB⟩
    · have HQ : ¬b / M < L := by
        rw [Nat.div_lt_iff_lt_mul hm]
        exact HB
      rw [integerEntry, dite_eq_left HA, dite_eq_right HB]
      simp [table, integerEntry, HQ]
  · have HQ : ¬a / M < L := by
      rw [Nat.div_lt_iff_lt_mul hm]
      exact HA
    rw [integerEntry, dite_eq_right HA]
    simp [table, integerEntry, HQ]

end LeanCanny.Algebra.IntegralNaturalBlockEntry

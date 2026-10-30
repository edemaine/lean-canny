/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateAffinePrefix

/-! # Independent affine normals from actual coordinate-prefix records

The height rows are coordinate normals and the selected objective is outside
their prefix. Their independence is thus proved directly from the generated
records, independently of the levels and the source roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateAffineSliceControls
open LeanCanny.Algebra LeanCanny.Geometry
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

lemma normal (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j i : Fin (P.dim u + 4)) :
    FlatAffineFullSourceTower.direction (CoordinateAffinePrefix.inputs P depth objective level) u k j.succ i =
      FermatCoordinateCone.normal j i :=
  CoordinateAffineTower.normal P depth objective (CoordinateAffinePrefix.levels P objective level) u k j i

theorem normals_independent (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) :
    ∀ c : FlatAffineFullSourceTower.free (CoordinateAffinePrefix.inputs P depth objective level) u k → ℝ,
      (∀ i, ∑ j : FlatAffineFullSourceTower.free (CoordinateAffinePrefix.inputs P depth objective level) u k,
        c j * (FlatAffineFullSourceTower.direction (CoordinateAffinePrefix.inputs P depth objective level) u k j.val.succ i : ℝ) = 0) →
      ∀ j, c j = 0 := by
  intro c hc t
  have HS : (∑ j : FlatAffineFullSourceTower.free (CoordinateAffinePrefix.inputs P depth objective level) u k,
      c j * (FlatAffineFullSourceTower.direction (CoordinateAffinePrefix.inputs P depth objective level) u k j.val.succ t.val : ℝ)) = c t := by
    rw [Finset.sum_eq_single t]
    · simp only [normal, FermatCoordinateCone.normal, ite_true, Int.cast_one, mul_one]
    · intro j _ hj
      have HJ : t.val ≠ j.val := fun he => hj (Subtype.ext he.symm)
      simp only [normal, FermatCoordinateCone.normal, HJ, ite_false, Int.cast_zero, mul_zero]
    · intro H
      exact False.elim (H (Finset.mem_univ t))
  exact HS.symm.trans (hc t.val)

theorem objective_independent (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) :
    ¬∃ c : FlatAffineFullSourceTower.free (CoordinateAffinePrefix.inputs P depth objective level) u k → ℝ,
      ∀ i, (FlatAffineFullSourceTower.direction (CoordinateAffinePrefix.inputs P depth objective level) u k 0 i : ℝ) =
        ∑ j : FlatAffineFullSourceTower.free (CoordinateAffinePrefix.inputs P depth objective level) u k,
          c j * (FlatAffineFullSourceTower.direction (CoordinateAffinePrefix.inputs P depth objective level) u k j.val.succ i : ℝ) := by
  rintro ⟨c, hc⟩
  let r := CoordinateAffineTower.selected P objective u k
  have HR : r ∉ FlatAffineFullSourceTower.free (CoordinateAffinePrefix.inputs P depth objective level) u k := by
    intro h
    exact (Nat.lt_irrefl r.val) ((CoordinateAffinePrefix.active_iff P depth objective level u k r).mp h)
  have H := hc r
  have HS : (∑ j : FlatAffineFullSourceTower.free (CoordinateAffinePrefix.inputs P depth objective level) u k,
      c j * (FlatAffineFullSourceTower.direction (CoordinateAffinePrefix.inputs P depth objective level) u k j.val.succ r : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have HJ : r ≠ j.val := fun he => HR (he.symm ▸ j.property)
    simp only [normal, FermatCoordinateCone.normal, HJ, ite_false, Int.cast_zero, mul_zero]
  rw [HS] at H
  have HO : FlatAffineFullSourceTower.direction (CoordinateAffinePrefix.inputs P depth objective level) u k 0 r = 1 := by
    exact (CoordinateAffineTower.objective P depth objective (CoordinateAffinePrefix.levels P objective level) u k r).trans
      (by simp only [r, FermatCoordinateCone.normal, ite_true])
  rw [HO, Int.cast_one] at H
  exact one_ne_zero H

end LeanCanny.Encoding.CoordinateAffineSliceControls

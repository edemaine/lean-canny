/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffinePrefix
public import LeanCanny.Geometry.ScaledCoordinateIndependence

/-! # Independent normals from the actual doubled midpoint records -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineSliceControls
open LeanCanny.Algebra LeanCanny.Geometry
open CoordinateDoubleAffinePrefix (inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem cast_twice_normal {n : ℕ} (r i : Fin n) :
    ((2 * FermatCoordinateCone.normal r i : ℤ) : ℝ) = 2 * FermatCoordinateCone.normal r i := by
  by_cases hi : i = r <;>
    simp only [FermatCoordinateCone.normal, hi, ite_true, ite_false, mul_one, mul_zero, Int.cast_ofNat, Int.cast_zero]

theorem normal_real (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j i : Fin (P.dim u + 4)) :
    (FlatAffineFullSourceTower.direction (inputs P depth objective level) u k j.succ i : ℝ) =
      2 * FermatCoordinateCone.normal j i :=
  (congrArg (fun z : ℤ => (z : ℝ)) (CoordinateDoubleAffinePrefix.normal P depth objective level u k j i)).trans (cast_twice_normal j i)

theorem objective_real (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (i : Fin (P.dim u + 4)) :
    (FlatAffineFullSourceTower.direction (inputs P depth objective level) u k 0 i : ℝ) =
      2 * FermatCoordinateCone.normal (CoordinateAffineTower.selected P objective u k) i :=
  (congrArg (fun z : ℤ => (z : ℝ)) (CoordinateDoubleAffinePrefix.objective P depth objective level u k i)).trans (cast_twice_normal _ i)

theorem normals_independent (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) :
    ∀ c : FlatAffineFullSourceTower.free (inputs P depth objective level) u k → ℝ,
      (∀ i, ∑ j : FlatAffineFullSourceTower.free (inputs P depth objective level) u k,
        c j * (FlatAffineFullSourceTower.direction (inputs P depth objective level) u k j.val.succ i : ℝ) = 0) → ∀ j, c j = 0 := by
  intro c hc
  apply ScaledCoordinateIndependence.normals _ (fun _ => 2) (fun _ => by norm_num) c
  intro i
  have HS : (∑ j : FlatAffineFullSourceTower.free (inputs P depth objective level) u k,
      c j * (FlatAffineFullSourceTower.direction (inputs P depth objective level) u k j.val.succ i : ℝ)) =
      ∑ j : FlatAffineFullSourceTower.free (inputs P depth objective level) u k,
        c j * (2 * FermatCoordinateCone.normal j.val i) :=
    Finset.sum_congr rfl (fun j _ => congrArg (fun z : ℝ => c j * z) (normal_real P depth objective level u k j.val i))
  exact HS.symm.trans (hc i)

theorem objective_independent (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) :
    ¬∃ c : FlatAffineFullSourceTower.free (inputs P depth objective level) u k → ℝ,
      ∀ i, (FlatAffineFullSourceTower.direction (inputs P depth objective level) u k 0 i : ℝ) =
        ∑ j : FlatAffineFullSourceTower.free (inputs P depth objective level) u k,
          c j * (FlatAffineFullSourceTower.direction (inputs P depth objective level) u k j.val.succ i : ℝ) := by
  rintro ⟨c, hc⟩
  let r := CoordinateAffineTower.selected P objective u k
  have HR : r ∉ FlatAffineFullSourceTower.free (inputs P depth objective level) u k := by
    intro h
    exact (Nat.lt_irrefl r.val) ((CoordinateDoubleAffinePrefix.active_iff P depth objective level u k r).mp h)
  apply ScaledCoordinateIndependence.objective _ (fun _ => 2) r HR 2 (by norm_num)
  refine ⟨c, ?_⟩
  intro i
  have HS : (∑ j : FlatAffineFullSourceTower.free (inputs P depth objective level) u k,
      c j * (FlatAffineFullSourceTower.direction (inputs P depth objective level) u k j.val.succ i : ℝ)) =
      ∑ j : FlatAffineFullSourceTower.free (inputs P depth objective level) u k,
        c j * (2 * FermatCoordinateCone.normal j.val i) :=
    Finset.sum_congr rfl (fun j _ => congrArg (fun z : ℝ => c j * z) (normal_real P depth objective level u k j.val i))
  exact (objective_real P depth objective level u k i).symm.trans ((hc i).trans HS)

end LeanCanny.Encoding.CoordinateDoubleAffineSliceControls

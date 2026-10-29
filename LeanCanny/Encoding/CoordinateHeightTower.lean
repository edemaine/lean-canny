/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateHeightSemantics

/-! # Ancestral coordinate records in complete doubled towers

Prefix activation preserves the level payload. The actual decoder therefore
copies an ancestral coordinate exactly, or equates twice the current
coordinate to the sum of two ancestral coordinates.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffinePrefix
open LeanCanny.Algebra MvPolynomial
open FlatAffineFullSourceTower (stage)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

lemma level_eq_decode (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j : Fin (P.dim u + 4)) :
    FlatAffineFullSourceTower.level (inputs P depth objective level) u k j =
      CoordinateHeightRecord.decode (P.dim u + 4) k (level (FlatAffineFullSourceTower.levelQuery u k j.val)) := by
  rw [CoordinateHeightRecord.level_eq_decode _ _ _ _ rfl]
  let q := FlatAffineFullSourceTower.levelQuery u k j.val
  change CoordinateHeightRecord.decode (P.dim u + 4) k (CoordinateAffinePrefix.levels P objective level q) =
    CoordinateHeightRecord.decode (P.dim u + 4) k (level q)
  unfold CoordinateAffinePrefix.levels CoordinateAffinePrefix.setFlags
  simp only [pairFst_pair, pairSnd_pair, List.singleton_append]
  exact CoordinateHeightRecord.decode_setActive (P.dim u + 4) k (level q)
    (decide (Nat.fromBitsLE (pairSnd q) < CoordinateAffinePrefix.cut P objective q))

lemma level_height (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j : Fin (P.dim u + 4)) (ancestor : Fin k)
    (h : level (FlatAffineFullSourceTower.levelQuery u k j.val) =
      CoordinateHeightRecord.height (P.dim u + 4) j.val ancestor.val) :
    FlatAffineFullSourceTower.level (inputs P depth objective level) u k j =
      .height ancestor (fun i => 2 * FermatCoordinateCone.normal j i) := by
  rw [level_eq_decode, h, CoordinateHeightRecord.decode_height]
  congr 1
  funext i
  simp only [FermatCoordinateCone.normal, Fin.ext_iff, mul_ite, mul_one, mul_zero]

lemma level_midpoint (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j : Fin (P.dim u + 4)) (left right : Fin k)
    (h : level (FlatAffineFullSourceTower.levelQuery u k j.val) =
      CoordinateHeightRecord.midpoint (P.dim u + 4) j.val left.val right.val) :
    FlatAffineFullSourceTower.level (inputs P depth objective level) u k j =
      .midpoint left right (FermatCoordinateCone.normal j) := by
  rw [level_eq_decode, h, CoordinateHeightRecord.decode_midpoint]
  congr 1
  funext i
  simp only [FermatCoordinateCone.normal, Fin.ext_iff]

lemma height_coordinate (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j : Fin (P.dim u + 4)) (ancestor : Fin k)
    (h : level (FlatAffineFullSourceTower.levelQuery u k j.val) =
      CoordinateHeightRecord.height (P.dim u + 4) j.val ancestor.val)
    (x : FlatAffineCriticalTower.Ancestors (P.dim u + 4) k → ℝ) (y : Fin (P.dim u + 4) → ℝ)
    (he : (∑ i, (FlatAffineFullSourceTower.direction (inputs P depth objective level) u k j.succ i : ℝ) * y i) =
      (FlatAffineFullSourceTower.level (inputs P depth objective level) u k j).polynomial.eval₂ (Int.castRingHom ℝ) x) :
    y j = x (FlatAffineCriticalTower.oldAmbient k ancestor j) := by
  rw [level_height P depth objective level u k j ancestor h, FlatAffineCriticalTower.Level.eval_height] at he
  simp_rw [normal] at he
  have H : 2 * y j = 2 * x (FlatAffineCriticalTower.oldAmbient k ancestor j) := by
    simpa [FermatCoordinateCone.normal, apply_ite, ite_mul] using he
  linarith

lemma midpoint_coordinate (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j : Fin (P.dim u + 4)) (left right : Fin k)
    (h : level (FlatAffineFullSourceTower.levelQuery u k j.val) =
      CoordinateHeightRecord.midpoint (P.dim u + 4) j.val left.val right.val)
    (x : FlatAffineCriticalTower.Ancestors (P.dim u + 4) k → ℝ) (y : Fin (P.dim u + 4) → ℝ)
    (he : (∑ i, (FlatAffineFullSourceTower.direction (inputs P depth objective level) u k j.succ i : ℝ) * y i) =
      (FlatAffineFullSourceTower.level (inputs P depth objective level) u k j).polynomial.eval₂ (Int.castRingHom ℝ) x) :
    2 * y j = x (FlatAffineCriticalTower.oldAmbient k left j) + x (FlatAffineCriticalTower.oldAmbient k right j) := by
  rw [level_midpoint P depth objective level u k j left right h, FlatAffineCriticalTower.Level.eval_midpoint] at he
  simp_rw [normal] at he
  simpa [FermatCoordinateCone.normal, apply_ite, ite_mul] using he

/-- Every original critical-stage root satisfies the exact midpoint relation
on an active coordinate carrying a midpoint record. -/
lemma root_midpoint_coordinate (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j : Fin (P.dim u + 4)) (left right : Fin k)
    (h : level (FlatAffineFullSourceTower.levelQuery u k j.val) =
      CoordinateHeightRecord.midpoint (P.dim u + 4) j.val left.val right.val)
    (hj : j ∈ FlatAffineFullSourceTower.free (inputs P depth objective level) u k)
    (p : MvPolynomial (Fin (P.dim u + 4)) ℤ)
    (x : FlatAffineCriticalTower.Ancestors (P.dim u + 4) k → ℝ) (y : Fin (P.dim u + 4) → ℝ)
    (mu : Fin (P.dim u + 4 + 1) → ℝ)
    (hz : ∀ v, (FlatAffineCriticalStage.row p
      (FlatAffineFullSourceTower.free (inputs P depth objective level) u k)
      (FlatAffineFullSourceTower.direction (inputs P depth objective level) u k)
      (fun i => (FlatAffineFullSourceTower.level (inputs P depth objective level) u k i).polynomial) v).eval₂
        (Int.castRingHom ℝ) (Sum.elim x (Sum.elim y mu)) = 0) :
    2 * y j = x (FlatAffineCriticalTower.oldAmbient k left j) + x (FlatAffineCriticalTower.oldAmbient k right j) := by
  apply midpoint_coordinate P depth objective level u k j left right h x y
  have H := ((FlatAffineCriticalStage.roots_iff (Int.castRingHom ℝ) p
    (FlatAffineFullSourceTower.free (inputs P depth objective level) u k)
    (FlatAffineFullSourceTower.direction (inputs P depth objective level) u k)
    (fun i => (FlatAffineFullSourceTower.level (inputs P depth objective level) u k i).polynomial) _).mp hz).2.1 j hj
  exact H

lemma midpoint_between (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j : Fin (P.dim u + 4)) (left right : Fin k)
    (h : level (FlatAffineFullSourceTower.levelQuery u k j.val) =
      CoordinateHeightRecord.midpoint (P.dim u + 4) j.val left.val right.val)
    (x : FlatAffineCriticalTower.Ancestors (P.dim u + 4) k → ℝ) (y : Fin (P.dim u + 4) → ℝ)
    (he : (∑ i, (FlatAffineFullSourceTower.direction (inputs P depth objective level) u k j.succ i : ℝ) * y i) =
      (FlatAffineFullSourceTower.level (inputs P depth objective level) u k j).polynomial.eval₂ (Int.castRingHom ℝ) x)
    (hlt : x (FlatAffineCriticalTower.oldAmbient k left j) < x (FlatAffineCriticalTower.oldAmbient k right j)) :
    x (FlatAffineCriticalTower.oldAmbient k left j) < y j ∧ y j < x (FlatAffineCriticalTower.oldAmbient k right j) := by
  have H := midpoint_coordinate P depth objective level u k j left right h x y he
  constructor <;> linarith

end LeanCanny.Encoding.CoordinateDoubleAffinePrefix

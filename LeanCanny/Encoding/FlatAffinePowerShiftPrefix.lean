/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerPrefix
public import LeanCanny.Algebra.PositivePolynomialProjection

/-! # Frozen prefixes of an actual varying-height tower

Changing a row beyond the chosen prefix leaves every prefix equation intact.
The extra zero coordinate is retained as well. Every shifted root therefore
projects to a root of the original frozen prefix, including singular roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerShiftPrefix
open LeanCanny.Algebra MvPolynomial
open FlatAffineFullSourceTower (Inputs)
open FlatAffineCompleteRootStages (truncate)
open FlatAffinePowerPrefix (projection)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

lemma raw_rename (F : Inputs) (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u : List Bool)
    (i : Fin (FlatAffineFullSourceTower.count (truncate F d) u)) :
    rename (FlatAffinePowerTower.prefixIndex (hd u)) (FlatAffinePowerPositive.rawSystem (truncate F d) u i) =
      FlatAffinePowerPositive.rawSystem F u (FlatAffinePowerTower.prefixIndex (hd u) i) :=
  FlatAffinePowerTower.rename_prefix_system (hd u) (BoundedFullCriticalSamples.polynomial F.source u)
    (FlatAffinePowerControls.degree F u) (FlatAffineFullSourceTower.free F u) (FlatAffineFullSourceTower.direction F u)
    (FlatAffineFullSourceTower.level F u) i

lemma projection_comp (F : Inputs) (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u : List Bool) :
    projection F d hd u ∘ Fin.castSucc = Fin.castSucc ∘ FlatAffinePowerTower.prefixIndex (hd u) :=
  funext (FlatAffinePowerPrefix.projection_old F d hd u)

lemma rename_system (F : Inputs) (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u : List Bool)
    (i : Fin (FlatAffineFullSourcePositive.count (truncate F d) u)) :
    rename (projection F d hd u) (FlatAffinePowerPositive.system (truncate F d) u i) =
      FlatAffinePowerPositive.system F u (projection F d hd u i) :=
  PositivePolynomialSystem.rename_projection (FlatAffinePowerPositive.rawSystem (truncate F d) u)
    (FlatAffinePowerPositive.rawSystem F u) (FlatAffinePowerTower.prefixIndex (hd u)) (projection F d hd u)
    (projection_comp F d hd u) (FlatAffinePowerPrefix.projection_last F d hd u) (raw_rename F d hd u) i

lemma projection_ne_shift (F : Inputs) (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u : List Bool)
    (row : Fin (FlatAffineFullSourcePositive.count F u))
    (hlo : FlatAffineFullSourceTower.count (truncate F d) u ≤ row.val)
    (hhi : row.val < FlatAffineFullSourceTower.count F u)
    (i : Fin (FlatAffineFullSourcePositive.count (truncate F d) u)) : projection F d hd u i ≠ row := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro HE
    rw [FlatAffinePowerPrefix.projection_last] at HE
    have HV := congrArg Fin.val HE
    change FlatAffineFullSourceTower.count F u = row.val at HV
    omega
  · intro HE
    rw [FlatAffinePowerPrefix.projection_old] at HE
    have HV := congrArg Fin.val HE
    change j.val = row.val at HV
    have HJ := j.isLt
    omega

theorem roots_prefix (F : Inputs) (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u : List Bool)
    (row : Fin (FlatAffineFullSourcePositive.count F u))
    (hlo : FlatAffineFullSourceTower.count (truncate F d) u ≤ row.val)
    (hhi : row.val < FlatAffineFullSourceTower.count F u) (t : ℝ)
    (z : Fin (FlatAffineFullSourcePositive.count F u) → ℝ)
    (hz : ∀ i, (FlatAffinePowerPositive.system F u i).eval₂ (Int.castRingHom ℝ) z = if i = row then t else 0) :
    ∀ i, (FlatAffinePowerPositive.system (truncate F d) u i).eval₂ (Int.castRingHom ℝ) (z ∘ projection F d hd u) = 0 := by
  intro i
  have H := hz (projection F d hd u i)
  rw [ite_eq_right (projection_ne_shift F d hd u row hlo hhi i), ← rename_system, eval₂_rename] at H
  exact H

end LeanCanny.Encoding.FlatAffinePowerShiftPrefix

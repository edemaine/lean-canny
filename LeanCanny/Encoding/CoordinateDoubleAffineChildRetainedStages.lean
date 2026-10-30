/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineChildLevels

/-! # Retained critical stages of recursive coordinate children

Each added block uses the original slice objective and active coordinates.
Its levels refer only to the original parent. In particular, the complete
ancestor system of a fixed-height child is the original next critical system.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
open LeanCanny.Algebra
open FlatAffineFullSourceTower (stage)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

theorem selected_retained (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (u : List Bool) (k : ℕ) (hk : depth u ≤ k) (hl : k < childDepth midpoint depth u) :
    CoordinateAffineTower.selected P (objective midpoint depth old) u k =
      CoordinateAffineTower.selected P old u (depth u) := by
  apply Fin.ext
  change min (objective midpoint depth old (stage u k)) (P.dim u + 3) = _
  rw [objective_retained midpoint depth old u k hk hl]
  rfl

theorem free_retained (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ)
    (hk : depth u ≤ k) (hl : k < childDepth midpoint depth u) :
    FlatAffineFullSourceTower.free (inputs midpoint P depth old level) u k =
      FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u) := by
  ext j
  exact (CoordinateDoubleAffinePrefix.active_iff P (childDepth midpoint depth) (objective midpoint depth old)
    (levels midpoint P depth old level) u k j).trans
      ((Iff.of_eq (congrArg (fun r : Fin (P.dim u + 4) => j.val < r.val)
        (selected_retained midpoint P depth old u k hk hl))).trans
          (CoordinateDoubleAffinePrefix.active_iff P depth old level u (depth u) j).symm)

theorem direction_retained (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ)
    (hk : depth u ≤ k) (hl : k < childDepth midpoint depth u) :
    FlatAffineFullSourceTower.direction (inputs midpoint P depth old level) u k =
      FlatAffineFullSourceTower.direction (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u) := by
  funext r i
  change FlatAffineFullSourceTower.integer 2
      (CoordinateDoubleAffineRecord.record (P.dim (pairFst (stage u k)) + 4)
        (min (objective midpoint depth old (stage u k)) (P.dim (pairFst (stage u k)) + 3)))
      (r.val * (P.dim u + 4) + i.val) =
    FlatAffineFullSourceTower.integer 2
      (CoordinateDoubleAffineRecord.record (P.dim (pairFst (stage u (depth u))) + 4)
        (min (old (stage u (depth u))) (P.dim (pairFst (stage u (depth u))) + 3)))
      (r.val * (P.dim u + 4) + i.val)
  rw [objective_retained midpoint depth old u k hk hl]
  simp only [stage, pairFst_pair]

theorem level_retained (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ)
    (hk : depth u ≤ k) (hl : k < childDepth midpoint depth u) (j : Fin (P.dim u + 4)) :
    FlatAffineFullSourceTower.level (inputs midpoint P depth old level) u k j =
      FlatAffineCriticalTower.Level.extend hk
        (FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u) j) :=
  level_copy midpoint P depth old level u k hk j (Or.inl (Nat.ne_of_lt hl))

theorem height_family_row (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) :
    (FlatAffineFullSourceTower.family (inputs false P depth old level) u).row (depth u) =
      (FlatAffineFullSourceTower.family (CoordinateDoubleAffinePrefix.inputs P depth old level) u).row (depth u) := by
  have hh : depth u < childDepth false depth u := by change depth u < depth u + 1; omega
  have HF := free_retained false P depth old level u (depth u) (le_refl _) hh
  have HD := direction_retained false P depth old level u (depth u) (le_refl _) hh
  have HL := funext (fun j : Fin (P.dim u + 4) =>
    (level_retained false P depth old level u (depth u) (le_refl _) hh j).trans
      (FlatAffineCriticalTower.Level.extend_refl _))
  let build (s : Finset (Fin (P.dim u + 4))) (a : Fin (P.dim u + 4 + 1) → Fin (P.dim u + 4) → ℤ)
      (b : Fin (P.dim u + 4) → FlatAffineCriticalTower.Level (P.dim u + 4) (depth u) ℤ) :=
    fun i : Fin (FlatAffineCriticalTower.width (P.dim u + 4)) =>
      MvPolynomial.rename
        (Equiv.sumCongr (Equiv.refl (FlatAffineCriticalTower.Ancestors (P.dim u + 4) (depth u)))
          (FlatAffineCriticalTower.blockEquiv (P.dim u + 4)))
        (FlatAffineCriticalStage.row (BoundedFullCriticalSamples.polynomial P u) s a
          (fun j => (b j).polynomial) ((FlatAffineCriticalTower.blockEquiv (P.dim u + 4)).symm i))
  change build (FlatAffineFullSourceTower.free (inputs false P depth old level) u (depth u))
      (FlatAffineFullSourceTower.direction (inputs false P depth old level) u (depth u))
      (FlatAffineFullSourceTower.level (inputs false P depth old level) u (depth u)) =
    build (FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u))
      (FlatAffineFullSourceTower.direction (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u))
      (FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u))
  rw [HF, HD, HL]

theorem height_system (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) :
    FlatAffineFullSourceTower.system (inputs false P depth old level) u =
      FlatAffineFullSourceTower.system
        (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u := by
  apply TriangularPolynomialIndexing.system_congr _ _ (depth u + 1)
  intro j hj
  by_cases h : j < depth u
  · exact family_row_before false P depth old level u j h
  · have he : j = depth u := by omega
    subst j
    exact height_family_row P depth old level u

noncomputable def heightRoot (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u) :
    FlatAffinePowerSampleInput.OriginalRoots (inputs false P depth old level) u :=
  FlatAffineSlicePresentation.rootOfSystemEq _ _ (height_system P depth old level u).symm z

theorem heightRoot_val (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u) :
    (heightRoot P depth old level u z).val = z.val :=
  FlatAffineSlicePresentation.rootOfSystemEq_val _ _ (height_system P depth old level u).symm z

end LeanCanny.Encoding.CoordinateDoubleAffineChildRecords

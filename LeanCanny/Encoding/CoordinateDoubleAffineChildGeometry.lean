/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineChildLevels
public import LeanCanny.Encoding.FlatAffineSliceStep

/-! # Exact recursive slice domains for retained critical children

Projecting any child root recovers an original parent root, including at
singular stages. The child slice is the original slice with precisely one
additional coordinate equation. Its level comes from the native height or
midpoint record, with all older level values preserved.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
open Set LeanCanny.Algebra
open FlatAffineFullSourceTower (stage levelQuery)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

theorem depth_le (midpoint : Bool) (depth : List Bool → ℕ) (u : List Bool) :
    depth u ≤ childDepth midpoint depth u := Nat.le_add_right _ _

theorem project_val (F : FlatAffineFullSourceTower.Inputs) (d : List Bool → ℕ) (u : List Bool)
    (hd : d u ≤ F.depth u) (z : FlatAffinePowerSampleInput.OriginalRoots F u) :
    (FlatAffineCompleteRootStages.project F d u hd z).val =
      z.val ∘ FlatAffineCompleteRootStages.prefixIndex F d u hd := rfl

noncomputable def parent (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots (inputs midpoint P depth old level) u) :
    FlatAffinePowerSampleInput.OriginalRoots (CoordinateDoubleAffinePrefix.inputs P depth old level) u :=
  FlatAffineSlicePresentation.rootOfSystemEq _ _ (parent_system midpoint P depth old level u)
    (FlatAffineCompleteRootStages.project (inputs midpoint P depth old level) depth u (depth_le midpoint depth u) z)

theorem parent_val (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots (inputs midpoint P depth old level) u) :
    (parent midpoint P depth old level u z).val = z.val ∘
      TriangularPolynomialRows.prefixIndex (FlatAffineCriticalTower.width (P.dim u + 4))
        (depth u) (childDepth midpoint depth u) (depth_le midpoint depth u) :=
  (FlatAffineSlicePresentation.rootOfSystemEq_val _ _ (parent_system midpoint P depth old level u) _).trans
    (project_val (inputs midpoint P depth old level) depth u (depth_le midpoint depth u) z)

attribute [local irreducible] parent

theorem copied_level_value (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots (inputs midpoint P depth old level) u)
    (j : Fin (P.dim u + 4)) (hj : j.val ≠ coordinate P depth old u) :
    (FlatAffineFullSourceTower.level (inputs midpoint P depth old level) u (childDepth midpoint depth u) j).polynomial.eval₂
        (Int.castRingHom ℝ) (z.val ∘ TriangularPolynomialIndexing.enumerate
          (FlatAffineCriticalTower.width (P.dim u + 4)) (childDepth midpoint depth u)) =
      (FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u) j).polynomial.eval₂
        (Int.castRingHom ℝ) ((parent midpoint P depth old level u z).val ∘
          TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (P.dim u + 4)) (depth u)) := by
  have HL := level_copy midpoint P depth old level u (childDepth midpoint depth u) (depth_le midpoint depth u) j (Or.inr hj)
  have HE := congrArg (fun b : FlatAffineCriticalTower.Level (P.dim u + 4) (childDepth midpoint depth u) ℤ =>
    b.polynomial.eval₂ (Int.castRingHom ℝ) (z.val ∘ TriangularPolynomialIndexing.enumerate
      (FlatAffineCriticalTower.width (P.dim u + 4)) (childDepth midpoint depth u))) HL
  have HX := congrArg (fun x : Fin (depth u * FlatAffineCriticalTower.width (P.dim u + 4)) → ℝ =>
    (FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u) j).polynomial.eval₂
      (Int.castRingHom ℝ) (x ∘ TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (P.dim u + 4)) (depth u)))
    (parent_val midpoint P depth old level u z)
  exact HE.trans ((FlatAffineCriticalTower.Level.eval_extend_prefix (Int.castRingHom ℝ) (depth_le midpoint depth u)
    (FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u) j) z.val).trans HX.symm)

def coordinateFin (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ) (u : List Bool) : Fin (P.dim u + 4) :=
  ⟨coordinate P depth old u, by unfold coordinate; omega⟩

theorem newest_level (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) :
    FlatAffineFullSourceTower.level (inputs midpoint P depth old level) u (childDepth midpoint depth u)
        (coordinateFin P depth old u) =
      FlatAffineLevelRecordData.decode (P.dim u + 4) 2 (childDepth midpoint depth u)
        (FlatAffineLevelRecordData.data (newLevel midpoint P depth old u)) := by
  calc
    _ = FlatAffineLevelRecordData.decode (P.dim u + 4) 2 (childDepth midpoint depth u)
        (FlatAffineLevelRecordData.data (levels midpoint P depth old level
          (levelQuery u (childDepth midpoint depth u) (coordinate P depth old u)))) :=
      level_raw P (childDepth midpoint depth) (objective midpoint depth old) (levels midpoint P depth old level)
        u (childDepth midpoint depth u) (coordinateFin P depth old u)
    _ = _ := congrArg (fun r => FlatAffineLevelRecordData.decode (P.dim u + 4) 2 (childDepth midpoint depth u)
      (FlatAffineLevelRecordData.data r)) (levels_newest midpoint P depth old level u)

noncomputable def newValue (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (u : List Bool) (z : Fin (childDepth midpoint depth u * FlatAffineCriticalTower.width (P.dim u + 4)) → ℝ) : ℝ :=
  (FlatAffineLevelRecordData.decode (P.dim u + 4) 2 (childDepth midpoint depth u)
    (FlatAffineLevelRecordData.data (newLevel midpoint P depth old u))).polynomial.eval₂ (Int.castRingHom ℝ)
      (z ∘ TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (P.dim u + 4)) (childDepth midpoint depth u))

theorem slice_eq (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (hn : old (stage u (depth u)) < P.dim u + 3)
    (z : FlatAffinePowerSampleInput.OriginalRoots (inputs midpoint P depth old level) u) :
    FlatAffineCompleteComponentSamples.slice (inputs midpoint P depth old level) u z =
      {y | y ∈ FlatAffineCompleteComponentSamples.slice (CoordinateDoubleAffinePrefix.inputs P depth old level) u
        (parent midpoint P depth old level u z) ∧
        2 * y (coordinateFin P depth old u) = newValue midpoint P depth old u z.val} := by
  let n := P.dim u + 4
  let r := coordinateFin P depth old u
  let G := inputs midpoint P depth old level
  let F := CoordinateDoubleAffinePrefix.inputs P depth old level
  let s := FlatAffineFullSourceTower.free G u (childDepth midpoint depth u)
  let t := FlatAffineFullSourceTower.free F u (depth u)
  let a := fun j i : Fin n => FlatAffineFullSourceTower.direction G u (childDepth midpoint depth u) j.succ i
  let c := fun j i : Fin n => FlatAffineFullSourceTower.direction F u (depth u) j.succ i
  let b := fun j : Fin n => (FlatAffineFullSourceTower.level G u (childDepth midpoint depth u) j).polynomial.eval₂
    (Int.castRingHom ℝ) (z.val ∘ TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width n) (childDepth midpoint depth u))
  let d := fun j : Fin n => (FlatAffineFullSourceTower.level F u (depth u) j).polynomial.eval₂
    (Int.castRingHom ℝ) ((parent midpoint P depth old level u z).val ∘
      TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width n) (depth u))
  have hold (j : Fin n) : j ∈ t ↔ j.val < coordinate P depth old u :=
    CoordinateDoubleAffinePrefix.active_iff P depth old level u (depth u) j
  have hs : s = insert r t := by
    ext j
    have H := CoordinateDoubleAffinePrefix.active_iff P (childDepth midpoint depth) (objective midpoint depth old)
      (levels midpoint P depth old level) u (childDepth midpoint depth u) j
    have HR := newest_selected midpoint P depth old u hn
    have HE : j = r ↔ j.val = coordinate P depth old u := Fin.ext_iff
    exact H.trans (by rw [HR, Finset.mem_insert, HE, hold]; omega)
  have ha : a = c := by
    funext j i
    exact (CoordinateDoubleAffinePrefix.normal P (childDepth midpoint depth) (objective midpoint depth old)
      (levels midpoint P depth old level) u (childDepth midpoint depth u) j i).trans
        (CoordinateDoubleAffinePrefix.normal P depth old level u (depth u) j i).symm
  have hb : ∀ j ∈ t, b j = d j := by
    intro j hj
    have H := (hold j).mp hj
    exact copied_level_value midpoint P depth old level u z j (by omega)
  have hr (y : Fin n → ℝ) : (∑ i, (a r i : ℝ) * y i) = 2 * y r := by
    have H := congrArg (fun f : Fin n → ℤ => ∑ i, (f i : ℝ) * y i)
      (funext (CoordinateDoubleAffinePrefix.normal P (childDepth midpoint depth) (objective midpoint depth old)
        (levels midpoint P depth old level) u (childDepth midpoint depth u) r))
    exact H.trans (FlatAffineSlicePresentation.coordinate_sum r y)
  have hv : b r = newValue midpoint P depth old u z.val :=
    congrArg (fun q : FlatAffineCriticalTower.Level n (childDepth midpoint depth u) ℤ =>
      q.polynomial.eval₂ (Int.castRingHom ℝ) (z.val ∘ TriangularPolynomialIndexing.enumerate
        (FlatAffineCriticalTower.width n) (childDepth midpoint depth u)))
      (newest_level midpoint P depth old level u)
  have H := FlatAffineSlicePresentation.set_step (BoundedFullCriticalSamples.polynomial P u)
    s t r a c b d (newValue midpoint P depth old u z.val) hs ha hb hr hv
  exact (FlatAffineSlicePresentation.original G u z).trans
    (FlatAffineSlicePresentation.step_transport _ _ _ _ H
      (FlatAffineSlicePresentation.original F u (parent midpoint P depth old level u z)).symm)

end LeanCanny.Encoding.CoordinateDoubleAffineChildRecords

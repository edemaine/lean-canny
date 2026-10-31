/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceContext
public import LeanCanny.Encoding.CoordinateDoubleAffineChildLevels

/-! # Extended histories retain the actual recursive child equations -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Algebra
open FlatAffineFullSourceTower (stage levelQuery)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] objective levels depth append seedCoordinate

theorem extended_free (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (k : ℕ) (hk : k ≤ depth d (append midpoint q)) :
    FlatAffineFullSourceTower.free (extendedInputs midpoint P d old level) q k =
      FlatAffineFullSourceTower.free
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q k := by
  apply Finset.ext
  intro j
  have H1 := CoordinateDoubleAffinePrefix.active_iff (readers P)
    (CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d))
    (objective d old ∘ FlatAffineFullSourceContext.query (append midpoint))
    (levels P d old level ∘ FlatAffineFullSourceContext.levelQuery (append midpoint)) q k j
  have H2 := CoordinateDoubleAffinePrefix.active_iff (readers P)
    (CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d))
    (CoordinateDoubleAffineChildRecords.objective midpoint (depth d) (objective d old))
    (CoordinateDoubleAffineChildRecords.levels midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q k j
  simp only [CoordinateAffineTower.selected, Function.comp_apply, FlatAffineFullSourceContext.query_stage] at H1 H2
  have HE := congrArg (fun v => j.val < min v ((readers P).dim q + 3)) (objective_append midpoint d old q k hk)
  exact H1.trans ((Iff.of_eq HE).trans H2.symm)

theorem direction_record (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (k : ℕ)
    (r : Fin (P.dim q + 4 + 1)) (i : Fin (P.dim q + 4)) :
    FlatAffineFullSourceTower.direction (CoordinateDoubleAffinePrefix.inputs P d old level) q k r i =
      FlatAffineFullSourceTower.integer 2
        (CoordinateDoubleAffineRecord.record (P.dim q + 4) (min (old (stage q k)) (P.dim q + 3)))
          (r.val * (P.dim q + 4) + i.val) := by
  simp only [FlatAffineFullSourceTower.direction, CoordinateDoubleAffinePrefix.inputs,
    FlatAffineFullSourceTower.arity, stage, LeanCanny.pairFst_pair]

theorem extended_direction (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (k : ℕ) (hk : k ≤ depth d (append midpoint q)) :
    FlatAffineFullSourceTower.direction (extendedInputs midpoint P d old level) q k =
      FlatAffineFullSourceTower.direction
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q k := by
  funext r i
  have H1 := direction_record (readers P) (CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d))
    (objective d old ∘ FlatAffineFullSourceContext.query (append midpoint))
    (levels P d old level ∘ FlatAffineFullSourceContext.levelQuery (append midpoint)) q k r i
  have H2 := direction_record (readers P) (CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d))
    (CoordinateDoubleAffineChildRecords.objective midpoint (depth d) (objective d old))
    (CoordinateDoubleAffineChildRecords.levels midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q k r i
  simp only [Function.comp_apply, FlatAffineFullSourceContext.query_stage] at H1
  have H := congrArg (fun v => FlatAffineFullSourceTower.integer 2
    (CoordinateDoubleAffineRecord.record ((readers P).dim q + 4) (min v ((readers P).dim q + 3)))
      (r.val * ((readers P).dim q + 4) + i.val)) (objective_append midpoint d old q k hk)
  exact H1.trans (H.trans H2.symm)

theorem extended_level (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (k : ℕ)
    (hv : Valid P (seedCoordinate d old) q) (hk : k ≤ depth d (append midpoint q))
    (j : Fin ((readers P).dim q + 4)) :
    FlatAffineFullSourceTower.level (extendedInputs midpoint P d old level) q k j =
      FlatAffineFullSourceTower.level
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q k j := by
  have H1 := CoordinateDoubleAffineChildRecords.level_raw (readers P)
    (CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d))
    (objective d old ∘ FlatAffineFullSourceContext.query (append midpoint))
    (levels P d old level ∘ FlatAffineFullSourceContext.levelQuery (append midpoint)) q k j
  have H2 := CoordinateDoubleAffineChildRecords.level_raw (readers P)
    (CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d))
    (CoordinateDoubleAffineChildRecords.objective midpoint (depth d) (objective d old))
    (CoordinateDoubleAffineChildRecords.levels midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q k j
  simp only [Function.comp_apply, FlatAffineFullSourceContext.query_level] at H1
  have H := congrArg (fun r => FlatAffineLevelRecordData.decode ((readers P).dim q + 4) 2 k (FlatAffineLevelRecordData.data r))
    (levels_append midpoint P d old level q k j.val hv hk)
  exact H1.trans (H.trans H2.symm)

theorem extended_family_row (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (k : ℕ)
    (hv : Valid P (seedCoordinate d old) q) (hk : k ≤ depth d (append midpoint q)) :
    (FlatAffineFullSourceTower.family (extendedInputs midpoint P d old level) q).row k =
      (FlatAffineFullSourceTower.family
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q).row k := by
  have HF := extended_free midpoint P d old level q k hk
  have HD := extended_direction midpoint P d old level q k hk
  have HL := funext (extended_level midpoint P d old level q k hv hk)
  let build (s : Finset (Fin ((readers P).dim q + 4)))
      (a : Fin ((readers P).dim q + 4 + 1) → Fin ((readers P).dim q + 4) → ℤ)
      (b : Fin ((readers P).dim q + 4) → FlatAffineCriticalTower.Level ((readers P).dim q + 4) k ℤ) :=
    fun i : Fin (FlatAffineCriticalTower.width ((readers P).dim q + 4)) =>
      MvPolynomial.rename
        (Equiv.sumCongr (Equiv.refl (FlatAffineCriticalTower.Ancestors ((readers P).dim q + 4) k))
          (FlatAffineCriticalTower.blockEquiv ((readers P).dim q + 4)))
        (FlatAffineCriticalStage.row (BoundedFullCriticalSamples.polynomial (readers P) q) s a
          (fun j => (b j).polynomial) ((FlatAffineCriticalTower.blockEquiv ((readers P).dim q + 4)).symm i))
  change build (FlatAffineFullSourceTower.free (extendedInputs midpoint P d old level) q k)
      (FlatAffineFullSourceTower.direction (extendedInputs midpoint P d old level) q k)
      (FlatAffineFullSourceTower.level (extendedInputs midpoint P d old level) q k) =
    build (FlatAffineFullSourceTower.free
      (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q k)
      (FlatAffineFullSourceTower.direction
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q k)
      (FlatAffineFullSourceTower.level
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q k)
  rw [HF, HD, HL]

theorem extended_system (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hv : Valid P (seedCoordinate d old) q) :
    FlatAffineFullSourceTower.system (extendedInputs midpoint P d old level) q =
      FlatAffineFullSourceTower.system
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q := by
  apply TriangularPolynomialIndexing.system_congr
  intro k hk
  apply extended_family_row midpoint P d old level q k hv
  rw [depth_append]
  exact hk.le

end LeanCanny.Encoding.CoordinateDoubleAffineTrace

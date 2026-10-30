/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineChildLevels
public import LeanCanny.Encoding.FlatAffinePowerPrefix

/-! # Native original-parent labels for recursive coordinate children

Project a valid child word and re-encode its retained parent directly in the
original parent sampler. The complete powered parent tuple is retained; no
regularity condition or separately supplied projection reader is needed.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] SquareSampleProjectionChoice.value SquareSampleProjectionChoice.language
  SquareSampleCompleteVertices.Valid

theorem prefix_power_system (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) :
    FlatAffinePowerPositive.system (FlatAffineCompleteRootStages.truncate (inputs midpoint P depth old level) depth) u =
      FlatAffinePowerPositive.system (CoordinateDoubleAffinePrefix.inputs P depth old level) u := by
  have HS := funext (fun t : Fin (depth u) => show
      FlatAffineFullSourceTower.free (inputs midpoint P depth old level) u t.val =
        FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth old level) u t.val from by
    unfold FlatAffineFullSourceTower.free
    apply Finset.filter_congr
    intro j _
    rw [level_record_before midpoint P depth old level u t.val j.val t.isLt])
  have HD := funext (fun t : Fin (depth u) => direction_before midpoint P depth old level u t.val t.isLt)
  have HL := funext (fun t : Fin (depth u) => funext (level_before midpoint P depth old level u t.val t.isLt))
  let build (s : Fin (depth u) → Finset (Fin (P.dim u + 4)))
      (a : Fin (depth u) → Fin (P.dim u + 4 + 1) → Fin (P.dim u + 4) → ℤ)
      (b : (t : Fin (depth u)) → Fin (P.dim u + 4) → FlatAffineCriticalTower.Level (P.dim u + 4) t.val ℤ) :=
    PositivePolynomialSystem.system (FlatAffinePowerTower.system
      (BoundedFullCriticalSamples.polynomial P u) (FlatAffinePowerControls.degree (inputs midpoint P depth old level) u) s a b)
  change build (fun t => FlatAffineFullSourceTower.free (inputs midpoint P depth old level) u t.val)
      (fun t => FlatAffineFullSourceTower.direction (inputs midpoint P depth old level) u t.val)
      (fun t => FlatAffineFullSourceTower.level (inputs midpoint P depth old level) u t.val) =
    build (fun t => FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth old level) u t.val)
      (fun t => FlatAffineFullSourceTower.direction (CoordinateDoubleAffinePrefix.inputs P depth old level) u t.val)
      (fun t => FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u t.val)
  rw [HS, HD, HL]

theorem child_depth_le (midpoint : Bool) (depth : List Bool → ℕ) (u : List Bool) :
    depth u ≤ childDepth midpoint depth u := Nat.le_add_right _ _

noncomputable def childInput (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : SquareSampleInput.Inputs :=
  FlatAffinePowerSampleInput.input (inputs midpoint P depth old level) (cone midpoint P depth old level)

noncomputable def parentInput (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : SquareSampleInput.Inputs :=
  FlatAffinePowerSampleInput.input (CoordinateDoubleAffinePrefix.inputs P depth old level)
    (CoordinateDoubleAffinePrefix.coneCertificate P depth old level)

noncomputable def projection (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) :
    Fin ((parentInput P depth old level).count u) → Fin ((childInput midpoint P depth old level).count u) :=
  FlatAffinePowerPrefix.projection (inputs midpoint P depth old level) depth (child_depth_le midpoint depth) u

theorem projection_unary (midpoint : Bool) {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    UnaryFn (fun q => (SquareSampleProjectedThom.coordinate (childInput midpoint P depth old level)
      (parentInput P depth old level) (projection midpoint P depth old level) (pairFst q) (pairSnd q)).val) := by
  have hn := (FlatAffineFullSourceTower.count_unary (CoordinateDoubleAffinePrefix.access hP hd ho hl hA)).comp pairFst_mem_FP
  have hi := UnaryFn.fromBitsLE_min (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) hn
  have H := UnaryFn.ite (FPPred.lt hi hn) hi
    ((FlatAffineFullSourceTower.count_unary (access midpoint hP hd ho hl hA)).comp pairFst_mem_FP)
  apply H.of_eq
  intro q
  simp only [Function.comp_apply, SquareSampleProjectedThom.coordinate, SquareSampleInput.selected,
    parentInput, childInput, FlatAffinePowerSampleInput.input, FlatAffineFullSourcePositive.count,
    Nat.add_sub_cancel, projection, FlatAffinePowerPrefix.projection,
    FlatAffineFullSourceTower.count, FlatAffineFullSourceTower.stageWidth, FlatAffineFullSourceTower.arity,
    FlatAffineCompleteRootStages.truncate, inputs, CoordinateDoubleAffinePrefix.inputs]
  split_ifs <;> rfl

noncomputable def parentWord (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : List Bool → List Bool :=
  SquareSampleProjectionChoice.value (childInput midpoint P depth old level) (parentInput P depth old level)
    (projection midpoint P depth old level)

theorem parentWord_evaluator (midpoint : Bool) {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceFunction (parentWord midpoint P depth old level) :=
  SquareSampleProjectionChoice.evaluator
    (FlatAffinePowerSampleInput.access (access midpoint hP hd ho hl hA) (cone midpoint P depth old level))
    (FlatAffinePowerSampleInput.access (CoordinateDoubleAffinePrefix.access hP hd ho hl hA)
      (CoordinateDoubleAffinePrefix.coneCertificate P depth old level))
    (projection midpoint P depth old level) (projection_unary midpoint hP hd ho hl hA)

theorem parentWord_projects (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (x : SquareSampleComplete.Roots (childInput midpoint P depth old level) u) :
    ∀ i, ((parentInput P depth old level).system u i).eval₂ (Int.castRingHom ℝ)
      (x.val ∘ projection midpoint P depth old level u) = 0 := by
  have H := FlatAffinePowerPrefix.roots_prefix (Int.castRingHom ℝ) (inputs midpoint P depth old level) depth
    (child_depth_le midpoint depth) u x.val x.property
  intro i
  exact (congrArg (fun f => (f i).eval₂ (Int.castRingHom ℝ) (x.val ∘ projection midpoint P depth old level u))
    (prefix_power_system midpoint P depth old level u)).symm.trans (H i)

theorem parentWord_valid (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (childInput midpoint P depth old level) u w) :
    SquareSampleCompleteVertices.Valid (parentInput P depth old level) u (parentWord midpoint P depth old level (pair u w)) :=
  SquareSampleProjectionChoice.value_valid (childInput midpoint P depth old level) (parentInput P depth old level)
    (FlatAffinePowerSampleInput.complete (CoordinateDoubleAffinePrefix.inputs P depth old level) _)
    (projection midpoint P depth old level) (parentWord_projects midpoint P depth old level) u w hw

theorem parentWord_point (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (childInput midpoint P depth old level) u w) :
    (SquareSampleCompleteVertices.candidate (parentInput P depth old level) u
      (parentWord midpoint P depth old level (pair u w)) (parentWord_valid midpoint P depth old level u w hw)).val =
      (SquareSampleCompleteVertices.candidate (childInput midpoint P depth old level) u w hw).val ∘
        projection midpoint P depth old level u :=
  SquareSampleProjectionChoice.value_point (childInput midpoint P depth old level) (parentInput P depth old level)
    (FlatAffinePowerSampleInput.complete (CoordinateDoubleAffinePrefix.inputs P depth old level) _)
    (projection midpoint P depth old level) (parentWord_projects midpoint P depth old level) u w hw

end LeanCanny.Encoding.CoordinateDoubleAffineChildRecords

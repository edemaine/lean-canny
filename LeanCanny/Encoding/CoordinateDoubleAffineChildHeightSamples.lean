/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineChildOriginalSamples
public import LeanCanny.Encoding.CoordinateDoubleAffineChildRetainedStages

/-! # Computing a fixed-height child word from an original critical sample

The retained original next-stage system and its powered system are unchanged.
Native search re-encodes an existing critical sample directly as the ancestor
of its fixed-height child slice, preserving its full original tuple.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] SquareSampleProjectionChoice.value SquareSampleCompleteVertices.Valid heightRoot

theorem height_free (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (hk : k < depth u + 1) :
    FlatAffineFullSourceTower.free (inputs false P depth old level) u k =
      FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth old level) u k := by
  by_cases h : k < depth u
  · unfold FlatAffineFullSourceTower.free
    apply Finset.filter_congr
    intro j _
    rw [level_record_before false P depth old level u k j.val h]
  · have he : k = depth u := by omega
    subst k
    exact free_retained false P depth old level u (depth u) (le_refl _) hk

theorem height_direction (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (hk : k < depth u + 1) :
    FlatAffineFullSourceTower.direction (inputs false P depth old level) u k =
      FlatAffineFullSourceTower.direction (CoordinateDoubleAffinePrefix.inputs P depth old level) u k := by
  by_cases h : k < depth u
  · exact direction_before false P depth old level u k h
  · have he : k = depth u := by omega
    subst k
    exact direction_retained false P depth old level u (depth u) (le_refl _) hk

theorem height_level (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (hk : k < depth u + 1) (j : Fin (P.dim u + 4)) :
    FlatAffineFullSourceTower.level (inputs false P depth old level) u k j =
      FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u k j := by
  by_cases h : k < depth u
  · exact level_before false P depth old level u k h j
  · have he : k = depth u := by omega
    subst k
    exact (level_retained false P depth old level u (depth u) (le_refl _) hk j).trans
      (FlatAffineCriticalTower.Level.extend_refl _)

theorem height_power_system (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) :
    FlatAffinePowerPositive.system (inputs false P depth old level) u =
      FlatAffinePowerPositive.system
        (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u := by
  have HS := funext (fun t : Fin (depth u + 1) => height_free P depth old level u t.val t.isLt)
  have HD := funext (fun t : Fin (depth u + 1) => height_direction P depth old level u t.val t.isLt)
  have HL := funext (fun t : Fin (depth u + 1) => funext (height_level P depth old level u t.val t.isLt))
  let build (s : Fin (depth u + 1) → Finset (Fin (P.dim u + 4)))
      (a : Fin (depth u + 1) → Fin (P.dim u + 4 + 1) → Fin (P.dim u + 4) → ℤ)
      (b : (t : Fin (depth u + 1)) → Fin (P.dim u + 4) → FlatAffineCriticalTower.Level (P.dim u + 4) t.val ℤ) :=
    PositivePolynomialSystem.system (FlatAffinePowerTower.system
      (BoundedFullCriticalSamples.polynomial P u) (FlatAffinePowerControls.degree (inputs false P depth old level) u) s a b)
  change build (fun t => FlatAffineFullSourceTower.free (inputs false P depth old level) u t.val)
      (fun t => FlatAffineFullSourceTower.direction (inputs false P depth old level) u t.val)
      (fun t => FlatAffineFullSourceTower.level (inputs false P depth old level) u t.val) =
    build (fun t => FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth old level) u t.val)
      (fun t => FlatAffineFullSourceTower.direction (CoordinateDoubleAffinePrefix.inputs P depth old level) u t.val)
      (fun t => FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u t.val)
  rw [HS, HD, HL]

noncomputable def criticalInput (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : SquareSampleInput.Inputs :=
  FlatAffinePowerSampleInput.input (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level))
    (CoordinateDoubleAffinePrefix.coneCertificate P (fun u => depth u + 1) old level)

noncomputable def heightWord (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : List Bool → List Bool :=
  SquareSampleProjectionChoice.value (criticalInput P depth old level) (childInput false P depth old level) (fun _ i => i)

theorem heightWord_evaluator {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceFunction (heightWord P depth old level) := by
  have A := FlatAffinePowerSampleInput.access
    (CoordinateDoubleAffinePrefix.access hP (hd.add (UnaryFn.const 1)) ho hl hA)
    (CoordinateDoubleAffinePrefix.coneCertificate P (fun u => depth u + 1) old level)
  have B := FlatAffinePowerSampleInput.access (access false hP hd ho hl hA) (cone false P depth old level)
  exact SquareSampleProjectionChoice.evaluator A B (fun _ i => i) (SquareSampleCompleteCoordinateThom.coordinate_unary B)

theorem heightWord_projects (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (x : SquareSampleComplete.Roots (criticalInput P depth old level) u) :
    ∀ i, ((childInput false P depth old level).system u i).eval₂ (Int.castRingHom ℝ) (x.val ∘ (fun i => i)) = 0 := by
  intro i
  exact (congrArg (fun f => (f i).eval₂ (Int.castRingHom ℝ) x.val)
    (height_power_system P depth old level u)).trans (x.property i)

theorem heightWord_valid (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (criticalInput P depth old level) u w) :
    SquareSampleCompleteVertices.Valid (childInput false P depth old level) u (heightWord P depth old level (pair u w)) :=
  SquareSampleProjectionChoice.value_valid (criticalInput P depth old level) (childInput false P depth old level)
    (FlatAffinePowerSampleInput.complete (inputs false P depth old level) _) (fun _ i => i)
    (heightWord_projects P depth old level) u w hw

theorem heightWord_point (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (criticalInput P depth old level) u w) :
    (SquareSampleCompleteVertices.candidate (childInput false P depth old level) u
      (heightWord P depth old level (pair u w)) (heightWord_valid P depth old level u w hw)).val =
      (SquareSampleCompleteVertices.candidate (criticalInput P depth old level) u w hw).val :=
  SquareSampleProjectionChoice.value_point (criticalInput P depth old level) (childInput false P depth old level)
    (FlatAffinePowerSampleInput.complete (inputs false P depth old level) _) (fun _ i => i)
    (heightWord_projects P depth old level) u w hw

theorem heightWord_root (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (criticalInput P depth old level) u w) :
    FlatAffineCompleteVertices.vertexEquiv (inputs false P depth old level) (cone false P depth old level) u
        ⟨heightWord P depth old level (pair u w), heightWord_valid P depth old level u w hw⟩ =
      heightRoot P depth old level u
        (FlatAffineCompleteVertices.vertexEquiv
          (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level))
          (CoordinateDoubleAffinePrefix.coneCertificate P (fun u => depth u + 1) old level) u ⟨w, hw⟩) := by
  have HP := heightWord_point P depth old level u w hw
  have HE := congrArg (fun z : Fin ((criticalInput P depth old level).count u) → ℝ =>
    FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree (inputs false P depth old level) u) (z ∘ Fin.castSucc)) HP
  apply Subtype.ext
  exact HE.trans (heightRoot_val P depth old level u
    (FlatAffineCompleteVertices.vertexEquiv
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level))
      (CoordinateDoubleAffinePrefix.coneCertificate P (fun u => depth u + 1) old level) u ⟨w, hw⟩)).symm

end LeanCanny.Encoding.CoordinateDoubleAffineChildRecords

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSampleVertices
public import LeanCanny.Geometry.FlatAffineTowerGeometry

/-! # Regular prefixes of native complete affine sample roots

Changing the depth alone retains the original source, directions, levels,
and exact prefix rows. Projecting a regular full root gives a regular root
of every earlier tower. Each projected root therefore has a unique valid
short sample word; computing that word from the full label remains separate.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSamplePrefix
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs count stageWidth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatAffineFullSourceTower.system

noncomputable def truncate (F : Inputs) (depth : List Bool → ℕ) : Inputs := { F with depth := depth }

theorem access {F : Inputs} (h : F.Access) {d : List Bool → ℕ} (hd : UnaryFn d) : (truncate F d).Access :=
  ⟨h.source, hd, h.width, h.direction, h.level, h.sourceArity⟩

theorem family_eq (F : Inputs) (d : List Bool → ℕ) (u : List Bool) :
    FlatAffineFullSourceTower.family (truncate F d) u = FlatAffineFullSourceTower.family F u := rfl

theorem system_eq (F : Inputs) (d : List Bool → ℕ) (u : List Bool) :
    FlatAffineFullSourceTower.system (truncate F d) u =
      TriangularPolynomialIndexing.system (FlatAffineFullSourceTower.family F u) (d u) := by
  unfold FlatAffineFullSourceTower.system
  rfl

def prefixIndex (F : Inputs) (d : List Bool → ℕ) (u : List Bool) (hd : d u ≤ F.depth u) :
    Fin (count (truncate F d) u) → Fin (count F u) :=
  TriangularPolynomialRows.prefixIndex (stageWidth F u) (d u) (F.depth u) hd

theorem prefixIndex_value (F : Inputs) (d : List Bool → ℕ) (u : List Bool) (hd : d u ≤ F.depth u)
    (i : Fin (count (truncate F d) u)) : (prefixIndex F d u hd i).val = i.val := rfl

theorem roots (F : Inputs) (d : List Bool → ℕ) (u : List Bool) (hd : d u ≤ F.depth u)
    (z : Fin (count F u) → ℝ)
    (hz : ∀ i, (FlatAffineFullSourceTower.system F u i).eval₂ (Int.castRingHom ℝ) z = 0) :
    ∀ i, (FlatAffineFullSourceTower.system (truncate F d) u i).eval₂ (Int.castRingHom ℝ)
      (z ∘ prefixIndex F d u hd) = 0 := by
  rw [system_eq]
  unfold FlatAffineFullSourceTower.system at hz
  exact TriangularPolynomialStageRegularity.roots_prefix (Int.castRingHom ℝ)
    (FlatAffineFullSourceTower.family F u) (d u) (F.depth u) hd z hz

theorem regular (F : Inputs) (d : List Bool → ℕ) (u : List Bool) (hd : d u ≤ F.depth u)
    (z : Fin (count F u) → ℝ)
    (hz : (fderiv ℝ (fun v => fun i => (FlatAffineFullSourceTower.system F u i).eval₂ (Int.castRingHom ℝ) v)
      z).IsInvertible) :
    (fderiv ℝ (fun v => fun i => (FlatAffineFullSourceTower.system (truncate F d) u i).eval₂ (Int.castRingHom ℝ) v)
      (z ∘ prefixIndex F d u hd)).IsInvertible := by
  unfold FlatAffineFullSourceTower.system at hz
  apply (TriangularPolynomialRegularity.analytic_iff (Int.castRingHom ℝ) _ _).mpr
  rw [system_eq]
  exact TriangularPolynomialStageRegularity.regular_prefix (Int.castRingHom ℝ)
    (FlatAffineFullSourceTower.family F u) (d u) (F.depth u) hd z
    ((TriangularPolynomialRegularity.analytic_iff (Int.castRingHom ℝ) _ _).mp hz)

noncomputable def project (F : Inputs) (d : List Bool → ℕ) (u : List Bool) (hd : d u ≤ F.depth u)
    (z : FlatAffineSampleVertices.OriginalCandidates F u) :
    FlatAffineSampleVertices.OriginalCandidates (truncate F d) u :=
  ⟨⟨z.val.val ∘ prefixIndex F d u hd, roots F d u hd z.val.val z.val.property⟩,
    regular F d u hd z.val.val z.property⟩

theorem project_coordinate (F : Inputs) (d : List Bool → ℕ) (u : List Bool) (hd : d u ≤ F.depth u)
    (z : FlatAffineSampleVertices.OriginalCandidates F u) (i : Fin (count (truncate F d) u)) :
    (project F d u hd z).val.val i = z.val.val (prefixIndex F d u hd i) := rfl

theorem project_trans (F : Inputs) (d e : List Bool → ℕ) (u : List Bool)
    (he : e u ≤ d u) (hd : d u ≤ F.depth u) (z : FlatAffineSampleVertices.OriginalCandidates F u) :
    project (truncate F d) e u he (project F d u hd z) =
      project F e u (he.trans hd) z := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  rfl

noncomputable def word (F : Inputs) (d : List Bool → ℕ) (u : List Bool) (hd : d u ≤ F.depth u)
    (z : FlatAffineSampleVertices.OriginalCandidates F u) : List Bool :=
  FlatAffineSampleVertices.word (truncate F d) u (project F d u hd z)

theorem word_valid (F : Inputs) (d : List Bool → ℕ) (u : List Bool) (hd : d u ≤ F.depth u)
    (z : FlatAffineSampleVertices.OriginalCandidates F u) :
    FlatAffineSampleVertices.Valid (truncate F d) u (word F d u hd z) :=
  FlatAffineSampleVertices.word_valid (truncate F d) u (project F d u hd z)

theorem sample_word (F : Inputs) (d : List Bool → ℕ) (u : List Bool) (hd : d u ≤ F.depth u)
    (z : FlatAffineSampleVertices.OriginalCandidates F u) :
    FlatAffineSampleVertices.sample (truncate F d) u (word F d u hd z) (word_valid F d u hd z) =
      project F d u hd z :=
  FlatAffineSampleVertices.sample_word (truncate F d) u (project F d u hd z)

end LeanCanny.Encoding.FlatAffineSamplePrefix

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineCompleteVertices
public import LeanCanny.Algebra.FlatAffineTowerRegularity

/-! # Prefixes and extensions of complete original affine roots

Every original root projects to a root of each earlier tower and has a unique
complete prefix label. Appending any frozen-stage root gives a complete root
without a Jacobian condition. These label identities are geometric; computing
a prefix label from a full label is a separate task.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineCompleteRootStages
open LeanCanny.Algebra LeanCanny.Computation MvPolynomial
open FlatAffineFullSourceTower (Inputs count stageWidth arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def truncate (F : Inputs) (d : List Bool → ℕ) : Inputs := {F with depth := d}

theorem access {F : Inputs} (h : F.Access) {d : List Bool → ℕ} (hd : UnaryFn d) : (truncate F d).Access :=
  ⟨h.source, hd, h.width, h.direction, h.level, h.sourceArity⟩

theorem cone_prefix (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) :
    FlatAffinePowerPositive.ConeCertificate (truncate F d) := by
  intro u k
  exact hcone u ⟨k.val, k.isLt.trans_le (hd u)⟩

def prefixIndex (F : Inputs) (d : List Bool → ℕ) (u : List Bool) (hd : d u ≤ F.depth u) :
    Fin (count (truncate F d) u) → Fin (count F u) :=
  TriangularPolynomialRows.prefixIndex (stageWidth F u) (d u) (F.depth u) hd

noncomputable def project (F : Inputs) (d : List Bool → ℕ) (u : List Bool) (hd : d u ≤ F.depth u)
    (z : FlatAffinePowerSampleInput.OriginalRoots F u) :
    FlatAffinePowerSampleInput.OriginalRoots (truncate F d) u := by
  refine ⟨z.val ∘ prefixIndex F d u hd, ?_⟩
  exact TriangularPolynomialStageRegularity.roots_prefix (Int.castRingHom ℝ)
    (FlatAffineFullSourceTower.family F u) (d u) (F.depth u) hd z.val z.property

lemma project_trans (F : Inputs) (d e : List Bool → ℕ) (u : List Bool)
    (he : e u ≤ d u) (hd : d u ≤ F.depth u) (z : FlatAffinePowerSampleInput.OriginalRoots F u) :
    project (truncate F d) e u he (project F d u hd z) = project F e u (he.trans hd) z := by
  apply Subtype.ext
  funext i
  rfl

noncomputable def word (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots F u) :
    {w : List Bool // FlatAffineCompleteVertices.Valid (truncate F d) (cone_prefix F hcone d hd) u w} :=
  (FlatAffineCompleteVertices.vertexEquiv (truncate F d) (cone_prefix F hcone d hd) u).symm (project F d u (hd u) z)

lemma sample_word (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots F u) :
    FlatAffineCompleteVertices.vertexEquiv (truncate F d) (cone_prefix F hcone d hd) u (word F hcone d hd u z) =
      project F d u (hd u) z := Equiv.apply_symm_apply _ _

noncomputable def next (F : Inputs) := truncate F (fun u => F.depth u + 1)

noncomputable def extend (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (y : FlatAffineCriticalStage.Variables (arity F u) → ℝ)
    (hy : ∀ i, (FlatAffineCriticalStage.row (BoundedFullCriticalSamples.polynomial F.source u)
      (FlatAffineFullSourceTower.free F u (F.depth u)) (FlatAffineFullSourceTower.direction F u (F.depth u))
      (fun j => (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial) i).eval₂ (Int.castRingHom ℝ)
      (Sum.elim (x.val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)) y) = 0) :
    FlatAffinePowerSampleInput.OriginalRoots (next F) u :=
  ⟨FlatAffineTowerRegularity.appendPoint (F.depth u) x.val y,
    (FlatAffineTowerRegularity.roots_appendPoint_iff (Int.castRingHom ℝ)
      (BoundedFullCriticalSamples.polynomial F.source u) (FlatAffineFullSourceTower.free F u)
      (FlatAffineFullSourceTower.direction F u) (FlatAffineFullSourceTower.level F u) (F.depth u) x.val y).mpr
      ⟨x.property, hy⟩⟩

lemma extend_prefix (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (y : FlatAffineCriticalStage.Variables (arity F u) → ℝ) (hy) :
    project (next F) F.depth u (by change F.depth u ≤ F.depth u + 1; omega) (extend F u x y hy) = x := by
  apply Subtype.ext
  exact FlatAffineTowerRegularity.appendPoint_prefix (F.depth u) x.val y


noncomputable def newest (F : Inputs) (u : List Bool) (z : Fin (count (next F) u) → ℝ)
    (v : FlatAffineCriticalStage.Variables (arity F u)) : ℝ :=
  z (TriangularPolynomialRows.block (stageWidth F u) (F.depth u) (F.depth u + 1) (by omega)
    (FlatAffineCriticalTower.blockEquiv (arity F u) v))

lemma extend_newest (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (y : FlatAffineCriticalStage.Variables (arity F u) → ℝ) (hy) :
    newest F u (extend F u x y hy).val = y := by
  funext v
  exact FlatAffineTowerRegularity.appendPoint_new (F.depth u) x.val y v

lemma word_length (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots F u) :
    (word F hcone d hd u z).val.length =
      FlatAffineCompleteVertices.width (truncate F d) (cone_prefix F hcone d hd) u :=
  FlatAffineCompleteVertices.word_length _ _ _ _ (word F hcone d hd u z).property

end LeanCanny.Encoding.FlatAffineCompleteRootStages

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSamplePrefix
public import LeanCanny.Geometry.FlatAffineComponentSampling

/-! # Extending native sample roots by actual regular affine critical stages

A regular frozen child stage and a regular parent root combine into one
regular root of the complete shared tower. Its valid short label retains
the original parent coordinates. This supplies the sampling bridge for
compact regular slices when the critical stages themselves are regular.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSampleExtension
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation MvPolynomial
open FlatAffineFullSourceTower (Inputs arity stageWidth count)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def next (F : Inputs) := FlatAffineSamplePrefix.truncate F (fun u => F.depth u + 1)

theorem access {F : Inputs} (h : F.Access) : (next F).Access :=
  FlatAffineSamplePrefix.access h (h.depth.add (UnaryFn.const 1))

noncomputable def source (F : Inputs) (u : List Bool) := BoundedFullCriticalSamples.polynomial F.source u
noncomputable def active (F : Inputs) (u : List Bool) := FlatAffineFullSourceTower.free F u (F.depth u)
def direction (F : Inputs) (u : List Bool) := FlatAffineFullSourceTower.direction F u (F.depth u)
noncomputable def levels (F : Inputs) (u : List Bool) (j : Fin (arity F u)) :=
  (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial

noncomputable def ancestors (F : Inputs) (u : List Bool) (x : Fin (count F u) → ℝ) :
    FlatAffineCriticalTower.Ancestors (arity F u) (F.depth u) → ℝ :=
  x ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)

noncomputable def rows (F : Inputs) (u : List Bool) :=
  FlatAffineCriticalStage.row (source F u) (active F u) (direction F u) (levels F u)

noncomputable def point (F : Inputs) (u : List Bool) (x : Fin (count F u) → ℝ)
    (y : FlatAffineCriticalStage.Variables (arity F u) → ℝ) : Fin (count (next F) u) → ℝ :=
  FlatAffineTowerRegularity.appendPoint (F.depth u) x y

noncomputable def extend (F : Inputs) (u : List Bool)
    (x : FlatAffineSampleVertices.OriginalCandidates F u)
    (y : FlatAffineCriticalStage.Variables (arity F u) → ℝ)
    (hy : ∀ i, (rows F u i).eval₂ (Int.castRingHom ℝ) (Sum.elim (ancestors F u x.val.val) y) = 0)
    (hr : (fderiv ℝ (fun v => fun i => (rows F u i).eval₂ (Int.castRingHom ℝ)
      (Sum.elim (ancestors F u x.val.val) v)) y).IsInvertible) :
    FlatAffineSampleVertices.OriginalCandidates (next F) u := by
  refine ⟨⟨point F u x.val.val y, ?_⟩, ?_⟩
  · exact (FlatAffineTowerRegularity.roots_appendPoint_iff (Int.castRingHom ℝ) (source F u)
      (FlatAffineFullSourceTower.free F u) (FlatAffineFullSourceTower.direction F u)
      (FlatAffineFullSourceTower.level F u) (F.depth u) x.val.val y).mpr ⟨x.val.property, hy⟩
  · exact (FlatAffineTowerGeometry.analytic_appendPoint_iff (Int.castRingHom ℝ) (source F u)
      (FlatAffineFullSourceTower.free F u) (FlatAffineFullSourceTower.direction F u)
      (FlatAffineFullSourceTower.level F u) (F.depth u) x.val.val y).mpr ⟨x.property, hr⟩

theorem extend_prefix (F : Inputs) (u : List Bool)
    (x : FlatAffineSampleVertices.OriginalCandidates F u)
    (y : FlatAffineCriticalStage.Variables (arity F u) → ℝ) (hy hr) :
    FlatAffineSamplePrefix.project (next F) F.depth u (by change F.depth u ≤ F.depth u + 1; omega)
      (extend F u x y hy hr) = x := by
  apply Subtype.ext
  apply Subtype.ext
  exact FlatAffineTowerRegularity.appendPoint_prefix (F.depth u) x.val.val y

noncomputable def newest (F : Inputs) (u : List Bool) (z : Fin (count (next F) u) → ℝ)
    (v : FlatAffineCriticalStage.Variables (arity F u)) : ℝ :=
  z (TriangularPolynomialRows.block (stageWidth F u) (F.depth u) (F.depth u + 1) (by omega)
    (FlatAffineCriticalTower.blockEquiv (arity F u) v))

theorem extend_newest (F : Inputs) (u : List Bool)
    (x : FlatAffineSampleVertices.OriginalCandidates F u)
    (y : FlatAffineCriticalStage.Variables (arity F u) → ℝ) (hy hr) :
    newest F u (extend F u x y hy hr).val.val = y := by
  funext v
  exact FlatAffineTowerRegularity.appendPoint_new (F.depth u) x.val.val y v

theorem active_card_lt (F : Inputs) (u : List Bool)
    (z : FlatAffineSampleVertices.OriginalCandidates (next F) u) : (active F u).card < arity F u :=
  FlatAffineTowerGeometry.active_card_lt (Int.castRingHom ℝ) (source F u)
    (FlatAffineFullSourceTower.free F u) (FlatAffineFullSourceTower.direction F u)
    (FlatAffineFullSourceTower.level F u) (F.depth u + 1) z.val.val z.property (F.depth u) (by omega)

theorem no_child_of_all_active (F : Inputs) (u : List Bool) (h : active F u = Finset.univ) :
    ¬ Nonempty (FlatAffineSampleVertices.OriginalCandidates (next F) u) := by
  rintro ⟨z⟩
  have hc := active_card_lt F u z
  simp only [h, Finset.card_univ, Fintype.card_fin] at hc
  omega

noncomputable def slice (F : Inputs) (u : List Bool)
    (x : FlatAffineSampleVertices.OriginalCandidates F u) : Set (Fin (arity F u) → ℝ) :=
  {y | (source F u).eval₂ (Int.castRingHom ℝ) y = 0 ∧ ∀ j ∈ active F u,
    ∑ i, (Int.castRingHom ℝ) (direction F u j.succ i) * y i =
      (levels F u j).eval₂ (Int.castRingHom ℝ) (ancestors F u x.val.val)}

noncomputable def RegularChildren (F : Inputs) (u : List Bool)
    (x : FlatAffineSampleVertices.OriginalCandidates F u) : Prop :=
  ∀ y : FlatAffineCriticalStage.Variables (arity F u) → ℝ,
    (∀ i, (rows F u i).eval₂ (Int.castRingHom ℝ) (Sum.elim (ancestors F u x.val.val) y) = 0) →
    (fderiv ℝ (fun v => fun i => (rows F u i).eval₂ (Int.castRingHom ℝ)
      (Sum.elim (ancestors F u x.val.val) v)) y).IsInvertible

noncomputable def Children (F : Inputs) (u : List Bool)
    (x : FlatAffineSampleVertices.OriginalCandidates F u) :=
  {y : FlatAffineCriticalStage.Variables (arity F u) → ℝ //
    ∀ i, (rows F u i).eval₂ (Int.castRingHom ℝ) (Sum.elim (ancestors F u x.val.val) y) = 0}

noncomputable def childRoot (F : Inputs) (u : List Bool)
    (x : FlatAffineSampleVertices.OriginalCandidates F u) (h : RegularChildren F u x)
    (y : Children F u x) : FlatAffineSampleVertices.OriginalCandidates (next F) u :=
  extend F u x y.val y.property (h y.val y.property)

theorem childRoot_injective (F : Inputs) (u : List Bool)
    (x : FlatAffineSampleVertices.OriginalCandidates F u) (h : RegularChildren F u x) :
    Function.Injective (childRoot F u x h) := by
  intro y z he
  have H := congrArg (fun q : FlatAffineSampleVertices.OriginalCandidates (next F) u => newest F u q.val.val) he
  simp only [childRoot, extend_newest] at H
  exact Subtype.ext H

theorem finite_children (F : Inputs) (u : List Bool)
    (x : FlatAffineSampleVertices.OriginalCandidates F u) (h : RegularChildren F u x) :
    Finite (Children F u x) ∧ Nat.card (Children F u x) ≤ FlatAffineSampleVertices.count (next F) u := by
  let _ : Finite (SquareSampleParameters.RegularParameters (FlatAffineSampleInput.input (next F)) u) :=
    (SquareSampleParameters.finite_regular_parameters (FlatAffineSampleInput.input (next F)) u).1
  let _ : Finite (FlatAffineSampleVertices.OriginalCandidates (next F) u) :=
    Finite.of_equiv _ (FlatAffineSampleVertices.originalEquiv (next F) u)
  exact ⟨Finite.of_injective (childRoot F u x h) (childRoot_injective F u x h),
    (Nat.card_le_card_of_injective (childRoot F u x h) (childRoot_injective F u x h)).trans_eq
      (FlatAffineSampleVertices.count_eq_candidates (next F) u).symm⟩

/-- Each component is sampled by a child label retaining the given parent.
The critical-stage regularity hypothesis is explicit and distinct from
regularity of the affine slice itself. -/
theorem exists_joined_label (F : Inputs) (u : List Bool)
    (x : FlatAffineSampleVertices.OriginalCandidates F u)
    (hcompact : IsCompact (slice F u x))
    (hregular : ∀ y ∈ slice F u x, Function.Surjective
      (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ) (source F u) (active F u) (direction F u) y))
    (hindependent : ¬ ∃ c : active F u → ℝ, ∀ i,
      (Int.castRingHom ℝ) (direction F u 0 i) =
        ∑ j : active F u, c j * (Int.castRingHom ℝ) (direction F u j.val.succ i))
    (hstage : RegularChildren F u x) (z : Fin (arity F u) → ℝ) (hz : z ∈ slice F u x) :
    ∃ (w : List Bool) (hw : FlatAffineSampleVertices.Valid (next F) u w),
      FlatAffineSamplePrefix.project (next F) F.depth u (by change F.depth u ≤ F.depth u + 1; omega)
        (FlatAffineSampleVertices.sample (next F) u w hw) = x ∧
      JoinedIn (slice F u x) z (fun i => newest F u
        (FlatAffineSampleVertices.sample (next F) u w hw).val.val (Sum.inl i)) := by
  obtain ⟨y, μ, _hμ, hj, hy⟩ := FlatAffineComponentSampling.exists_joined_stage_root
    (Int.castRingHom ℝ) (source F u) (active F u) (direction F u) (levels F u)
    (ancestors F u x.val.val) hcompact (fun y hp hl => hregular y ⟨hp, hl⟩)
    hindependent z hz.1 hz.2
  let q := extend F u x (Sum.elim y μ) hy (hstage _ hy)
  let w := FlatAffineSampleVertices.word (next F) u q
  have hw : FlatAffineSampleVertices.Valid (next F) u w := FlatAffineSampleVertices.word_valid (next F) u q
  have hs : FlatAffineSampleVertices.sample (next F) u w hw = q := FlatAffineSampleVertices.sample_word (next F) u q
  refine ⟨w, hw, ?_, ?_⟩
  · rw [hs]
    exact extend_prefix F u x (Sum.elim y μ) hy (hstage _ hy)
  · rw [hs]
    change JoinedIn (slice F u x) z (fun i => newest F u (extend F u x (Sum.elim y μ) hy (hstage _ hy)).val.val (Sum.inl i))
    rw [extend_newest]
    exact hj

end LeanCanny.Encoding.FlatAffineSampleExtension

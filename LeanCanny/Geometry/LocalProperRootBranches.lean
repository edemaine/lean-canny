/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.LocalProperCovering
public import LeanCanny.Geometry.RootBranches

/-! # Root branches from properness on the retained interval

Auxiliary equations may acquire extra roots at exceptional endpoints. The
covering construction only needs properness and regularity on the open slab.
-/

@[expose] public section
namespace LeanCanny.Geometry.LocalProperRootBranches
open Set Topology
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma covering (f : ℝ × E → F) (a b : ℝ)
    (hp : IsProperMap (RootBranches.projection f a b))
    (hf : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b → ContDiffAt ℝ 1 f z.val)
    (hJac : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      (fderiv ℝ f z.val ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible) :
    IsCoveringMap (RootBranches.projection f a b) :=
  LocalProperCovering.covering_restrict (RootProjection.continuous_projection f) isOpen_Ioo hp
    (RootProjection.isLocalHomeomorphOn f (Ioo a b) hf hJac)

lemma finite_index (f : ℝ × E → F) (a b : ℝ) (t₀ : Ioo a b)
    (hp : IsProperMap (RootBranches.projection f a b))
    (hf : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b → ContDiffAt ℝ 1 f z.val)
    (hJac : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      (fderiv ℝ f z.val ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible) :
    Finite (RootBranches.Index f a b t₀) :=
  (LocalProperCovering.finite_fiber hp
    (LocalProperCovering.localHomeomorph_restrict (RootProjection.continuous_projection f) isOpen_Ioo
      (RootProjection.isLocalHomeomorphOn f (Ioo a b) hf hJac)) t₀).to_subtype

lemma exists_anchored_branches (f : ℝ × E → F) (a b : ℝ) (t₀ : Ioo a b)
    (hp : IsProperMap (RootBranches.projection f a b))
    (hf : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b → ContDiffAt ℝ 1 f z.val)
    (hJac : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      (fderiv ℝ f z.val ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible) :
    ∃ curve : RootBranches.Index f a b t₀ → C(Ioo a b, E),
      (∀ i, curve i t₀ = i.val.val.val.2) ∧
      (∀ i t, f (t.val, curve i t) = 0) ∧
      ∀ t : Ioo a b, ∀ x : E, f (t.val, x) = 0 ↔ ∃! i, curve i t = x :=
  RootBranches.exists_anchored_branches_of_covering f a b t₀ (covering f a b hp hf hJac)

end LeanCanny.Geometry.LocalProperRootBranches

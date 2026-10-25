/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RootProjection
public import LeanCanny.Geometry.CoveringBranches

/-! # Complete finite branches between critical parameter values

For a proper root projection with invertible derivative in the unknowns on
an open parameter interval, all roots on that interval split into finitely
many disjoint continuous branches. A single fiber indexes them. The local
charts, the covering property, global continuation, and completeness of the
enumeration are proved internally.

The remaining algebraic obligations are to construct suitable systems and
critical intervals, establish properness and regularity there, and bound the
encodings of the branches. This file supplies no such quantitative bound.
-/

@[expose] public section

namespace LeanCanny.Geometry.RootBranches
open Set Function Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

abbrev IntervalSpace (f : ℝ × E → F) (a b : ℝ) := RootProjection.projection f ⁻¹' Ioo a b

def projection (f : ℝ × E → F) (a b : ℝ) : IntervalSpace f a b → Ioo a b :=
  (Ioo a b).restrictPreimage (RootProjection.projection f)

abbrev Index (f : ℝ × E → F) (a b : ℝ) (t₀ : Ioo a b) := projection f a b ⁻¹' {t₀}

/-- The indexing fiber is finite as a consequence of properness and regularity. -/
theorem finite_index (f : ℝ × E → F) (a b : ℝ) (t₀ : Ioo a b)
    (hproper : IsProperMap (RootProjection.projection f))
    (hf : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      ContDiffAt ℝ 1 f z.val)
    (hJac : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      (fderiv ℝ f z.val ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible) :
    Finite (Index f a b t₀) := by
  have hfin := RootProjection.finite_fiber f t₀.val hproper
    (fun z hz => hf z (by rw [hz]; exact t₀.property))
    (fun z hz => hJac z (by rw [hz]; exact t₀.property))
  let g : Index f a b t₀ → (RootProjection.projection f ⁻¹' {t₀.val}) :=
    fun i => ⟨i.val.val, congrArg Subtype.val i.property⟩
  have : Finite (RootProjection.projection f ⁻¹' {t₀.val}) := hfin.to_subtype
  apply Finite.of_injective g
  intro i j hij
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun w : (RootProjection.projection f ⁻¹' {t₀.val}) => w.val) hij

/-- Complete, disjoint continuous root branches. Their index type is proved
finite by `finite_index`; their cardinality is not assumed as input. -/
theorem exists_branches (f : ℝ × E → F) (a b : ℝ) (t₀ : Ioo a b)
    (hproper : IsProperMap (RootProjection.projection f))
    (hf : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      ContDiffAt ℝ 1 f z.val)
    (hJac : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      (fderiv ℝ f z.val ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible) :
    ∃ curve : Index f a b t₀ → C(Ioo a b, E),
      (∀ i t, f (t.val, curve i t) = 0) ∧
      ∀ t : Ioo a b, ∀ x : E, f (t.val, x) = 0 ↔ ∃! i, curve i t = x := by
  have hcover := (RootProjection.isCoveringMapOn f (Ioo a b) hproper hf hJac).isCoveringMap_restrictPreimage
  obtain ⟨branch, _, hproj, hcomplete⟩ := CoveringBranches.exists_interval_branches hcover t₀
  let curve : Index f a b t₀ → C(Ioo a b, E) := fun i =>
    ⟨fun t => (branch i t).val.val.2,
      continuous_snd.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp (branch i).continuous))⟩
  have hparameter (i : Index f a b t₀) (t : Ioo a b) : (branch i t).val.val.1 = t.val :=
    congrArg Subtype.val (hproj i t)
  refine ⟨curve, ?_, ?_⟩
  · intro i t
    have hroot := (branch i t).val.property
    have hz : (branch i t).val.val = (t.val, curve i t) := Prod.ext (hparameter i t) rfl
    rwa [hz] at hroot
  · intro t x
    constructor
    · intro hx
      let z : IntervalSpace f a b := ⟨⟨(t.val, x), hx⟩, t.property⟩
      have hz : (Ioo a b).restrictPreimage (RootProjection.projection f) z = t := rfl
      obtain ⟨i, hi, huniq⟩ := hcomplete t z hz
      refine ⟨i, ?_, ?_⟩
      · exact congrArg (fun w : IntervalSpace f a b => w.val.val.2) hi
      · intro j hj
        apply huniq
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext (hparameter j t) hj
    · rintro ⟨i, hi, _⟩
      have hroot := (branch i t).val.property
      have hz : (branch i t).val.val = (t.val, x) := Prod.ext (hparameter i t) hi
      rwa [hz] at hroot

end LeanCanny.Geometry.RootBranches

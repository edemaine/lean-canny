/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FrontierCover
public import LeanCanny.Geometry.AlgebraicBranchLimit
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Accessible pieces from parametrized arcs

A continuous parametrization of a closed bounded interval makes the image of
its open interval accessible from every boundary point. The proof includes
noninjective parametrizations and does not require regularity of a derivative.
This supplies the geometric hypothesis of the frontier-incidence theorem for
curve arcs once their continuous endpoint extensions have been constructed.
-/

@[expose] public section

namespace LeanCanny.Connectivity.FrontierCover
open Set

/-- Linear interpolation from a closed-interval point to an interior point
stays in the interior after its starting time. -/
theorem joinedIn_insert_Ioo {a b x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Ioo a b) :
    JoinedIn (insert x (Ioo a b)) x y := by
  refine ⟨Path.ofLine (f := fun t : ℝ => (1 - t) * x + t * y)
    (by fun_prop) (by simp) (by simp), ?_⟩
  intro t
  change (1 - (t : ℝ)) * x + (t : ℝ) * y ∈ insert x (Ioo a b)
  by_cases ht : (t : ℝ) = 0
  · simp [ht]
  · right
    have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

theorem accessible_Ioo (a b : ℝ) : Accessible (Ioo a b) := by
  intro x hx y hy
  have hbound : x ∈ Icc a b := (closure_minimal Ioo_subset_Icc_self isClosed_Icc) hx
  exact joinedIn_insert_Ioo hbound hy

/-- The continuous image of an open arc admits access from every point of its
closure, provided the parametrization extends continuously to both ends. -/
theorem accessible_open_arc {X : Type*} [TopologicalSpace X] [T2Space X]
    {a b : ℝ} {f : ℝ → X} (hf : ContinuousOn f (Icc a b)) :
    Accessible (f '' Ioo a b) := by
  intro x hx y hy
  have hclosed : IsClosed (f '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hf).isClosed
  have hsub : f '' Ioo a b ⊆ f '' Icc a b := image_mono Ioo_subset_Icc_self
  obtain ⟨t, ht, rfl⟩ := (closure_minimal hsub hclosed) hx
  obtain ⟨u, hu, rfl⟩ := hy
  have hparam : insert t (Ioo a b) ⊆ Icc a b :=
    insert_subset ht Ioo_subset_Icc_self
  have hpath := (joinedIn_insert_Ioo ht hu).map (hf.mono hparam)
  simpa only [image_insert_eq] using hpath

/-- Bounded algebraic coordinate relations supply endpoint access without
assuming that the arc has a nonsingular endpoint. -/
theorem accessible_algebraic_arc {ι : Type*} {a b : ℝ} {f : ℝ → ι → ℝ}
    (hab : a < b) (hf : ContinuousOn f (Ioo a b))
    (p : ι → Polynomial (Polynomial ℝ)) (hp : ∀ i, p i ≠ 0)
    (K : ι → Set ℝ) (hK : ∀ i, IsCompact (K i))
    (hbound : ∀ t ∈ Ioo a b, ∀ i, f t i ∈ K i)
    (hzero : ∀ t ∈ Ioo a b, ∀ i, Geometry.AlgebraicBranchLimit.value (p i) t (f t i) = 0) :
    Accessible (f '' Ioo a b) := by
  obtain ⟨g, hg, heq⟩ := Geometry.AlgebraicBranchLimit.continuous_extension
    hab hf p hp K hK hbound hzero
  rw [← image_congr heq]
  exact accessible_open_arc hg

end LeanCanny.Connectivity.FrontierCover

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RootBranches
public import LeanCanny.Connectivity.AccessibleArc
public import LeanCanny.Connectivity.SlabCover

/-! # Finite complete algebraic arcs on a regular slab

Regularity constructs local root charts, properness gives a finite covering,
and covering lifts give complete global branches between critical slices.
Nonzero coordinate equations extend these branches to both endpoint slices.
Properness itself supplies the coordinate compact bounds needed for those
extensions. All arc points, including endpoints, satisfy the original system.

The coordinate equations, regular interval and properness still need to be
established for the effective roadmap systems. No representation-size or
polynomial-space construction theorem is asserted in this module.
-/

@[expose] public section

namespace LeanCanny.Connectivity.RegularRootArcs
open Set Function Topology
open Geometry

variable {ι F : Type*} [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- An actual family of complete, disjoint root arcs with accessible boundary.
The index is the finite fiber proved in `RootBranches.finite_index`. -/
theorem exists_anchored_arcs (f : ℝ × (ι → ℝ) → F) (a b : ℝ) (t₀ : Ioo a b)
    (hcont : Continuous f) (hproper : IsProperMap (RootProjection.projection f))
    (hf : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      ContDiffAt ℝ 1 f z.val)
    (hJac : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      (fderiv ℝ f z.val ∘L ContinuousLinearMap.inr ℝ ℝ (ι → ℝ)).IsInvertible)
    (p : ι → Polynomial (Polynomial ℝ)) (hp : ∀ i, p i ≠ 0)
    (hrel : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      ∀ i, AlgebraicBranchLimit.value (p i) z.val.1 (z.val.2 i) = 0) :
    ∃ curve : RootBranches.Index f a b t₀ → ℝ → ι → ℝ,
      (∀ j, curve j t₀.val = j.val.val.val.2) ∧
      (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
      (∀ j t, t ∈ Icc a b → f (t, curve j t) = 0) ∧
      (∀ t : Ioo a b, ∀ x, f (t.val, x) = 0 ↔ ∃! j, curve j t.val = x) ∧
      ∀ j, FrontierCover.Accessible ((fun t => (t, curve j t)) '' Ioo a b) := by
  classical
  have hab : a < b := t₀.property.1.trans t₀.property.2
  obtain ⟨branch, hanchor, hroots, hcomplete⟩ :=
    RootBranches.exists_anchored_branches f a b t₀ hproper hf hJac
  let K : ι → Set ℝ := fun i =>
    (fun z : RootProjection.Space f => z.val.2 i) '' (RootProjection.projection f ⁻¹' Icc a b)
  have hK (i : ι) : IsCompact (K i) :=
    (hproper.isCompact_preimage isCompact_Icc).image
      ((continuous_apply i).comp (continuous_snd.comp continuous_subtype_val))
  let total : RootBranches.Index f a b t₀ → ℝ → ι → ℝ := fun j t =>
    if ht : t ∈ Ioo a b then branch j ⟨t, ht⟩ else 0
  have htval (j : RootBranches.Index f a b t₀) (t : Ioo a b) : total j t.val = branch j t := by
    simp only [total, dite_eq_left t.property]
  have htcont (j : RootBranches.Index f a b t₀) : ContinuousOn (total j) (Ioo a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply (branch j).continuous.congr
    intro t
    exact (htval j t).symm
  have htbound (j : RootBranches.Index f a b t₀) (t : ℝ) (ht : t ∈ Ioo a b) (i : ι) :
      total j t i ∈ K i := by
    let z : RootProjection.Space f := ⟨(t, branch j ⟨t, ht⟩), hroots j ⟨t, ht⟩⟩
    refine ⟨z, Ioo_subset_Icc_self ht, ?_⟩
    rw [htval j ⟨t, ht⟩]
  have htzero (j : RootBranches.Index f a b t₀) (t : ℝ) (ht : t ∈ Ioo a b) (i : ι) :
      AlgebraicBranchLimit.value (p i) t (total j t i) = 0 := by
    rw [htval j ⟨t, ht⟩]
    exact hrel ⟨(t, branch j ⟨t, ht⟩), hroots j ⟨t, ht⟩⟩ ht i
  have hext (j : RootBranches.Index f a b t₀) := AlgebraicBranchLimit.continuous_extension
    hab (htcont j) p hp K hK (htbound j) (htzero j)
  choose curve hc heq using hext
  have hvalue (j : RootBranches.Index f a b t₀) (t : Ioo a b) : curve j t.val = branch j t :=
    (heq j t.property).trans (htval j t)
  have hfullroot (j : RootBranches.Index f a b t₀) (t : ℝ) (ht : t ∈ Icc a b) :
      f (t, curve j t) = 0 := by
    let γ : ℝ → ℝ × (ι → ℝ) := fun t => (t, curve j t)
    have hγ : ContinuousOn γ (Icc a b) := continuous_id.continuousOn.prodMk (hc j)
    have htcl : t ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
    have hcl : γ t ∈ closure (γ '' Ioo a b) :=
      ((hγ t ht).mono Ioo_subset_Icc_self).mem_closure_image htcl
    have hsub : γ '' Ioo a b ⊆ {z | f z = 0} := by
      rintro z ⟨s, hs, rfl⟩
      change f (s, curve j s) = 0
      rw [hvalue j ⟨s, hs⟩]
      exact hroots j ⟨s, hs⟩
    exact (closure_minimal hsub (isClosed_eq hcont continuous_const)) hcl
  refine ⟨curve, (fun j => (hvalue j t₀).trans (hanchor j)), hc, hfullroot, ?_, ?_⟩
  · intro t x
    simpa only [hvalue] using hcomplete t x
  · intro j
    exact FrontierCover.accessible_open_arc (continuous_id.continuousOn.prodMk (hc j))

/-- Complete accessible root arcs; `exists_anchored_arcs` also identifies each
label with its actual root at the sample parameter. -/
theorem exists_arcs (f : ℝ × (ι → ℝ) → F) (a b : ℝ) (t₀ : Ioo a b)
    (hcont : Continuous f) (hproper : IsProperMap (RootProjection.projection f))
    (hf : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      ContDiffAt ℝ 1 f z.val)
    (hJac : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      (fderiv ℝ f z.val ∘L ContinuousLinearMap.inr ℝ ℝ (ι → ℝ)).IsInvertible)
    (p : ι → Polynomial (Polynomial ℝ)) (hp : ∀ i, p i ≠ 0)
    (hrel : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      ∀ i, AlgebraicBranchLimit.value (p i) z.val.1 (z.val.2 i) = 0) :
    ∃ curve : RootBranches.Index f a b t₀ → ℝ → ι → ℝ,
      (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
      (∀ j t, t ∈ Icc a b → f (t, curve j t) = 0) ∧
      (∀ t : Ioo a b, ∀ x, f (t.val, x) = 0 ↔ ∃! j, curve j t.val = x) ∧
      ∀ j, FrontierCover.Accessible ((fun t => (t, curve j t)) '' Ioo a b) := by
  obtain ⟨curve, _, hc, hroot, hcomplete, haccess⟩ :=
    exists_anchored_arcs f a b t₀ hcont hproper hf hJac p hp hrel
  exact ⟨curve, hc, hroot, hcomplete, haccess⟩

/-- Construct the complete accessible slab decomposition from a proper regular
root system and covers of its endpoint fibers. Interior branches are derived
from the equations, and their number is finite without an enumeration oracle. -/
theorem exists_slab_cover {L R : Type*}
    (f : ℝ × (ι → ℝ) → F) (a b : ℝ) (t₀ : Ioo a b)
    (hcont : Continuous f) (hproper : IsProperMap (RootProjection.projection f))
    (hf : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      ContDiffAt ℝ 1 f z.val)
    (hJac : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      (fderiv ℝ f z.val ∘L ContinuousLinearMap.inr ℝ ℝ (ι → ℝ)).IsInvertible)
    (p : ι → Polynomial (Polynomial ℝ)) (hp : ∀ i, p i ≠ 0)
    (hrel : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      ∀ i, AlgebraicBranchLimit.value (p i) z.val.1 (z.val.2 i) = 0)
    (left : SlabCover.FiberCover (fun t x => f (t, x) = 0) a L)
    (right : SlabCover.FiberCover (fun t x => f (t, x) = 0) b R) :
    Finite (RootBranches.Index f a b t₀) ∧
      ∃ curve : RootBranches.Index f a b t₀ → ℝ → ι → ℝ,
        let piece := SlabCover.piece (fun t x => f (t, x) = 0)
          curve left.piece right.piece a b
        (∀ z, ∃ i, z ∈ piece i) ∧ (∀ i, FrontierCover.Accessible (piece i)) ∧
        (∀ j l, FrontierCover.Incident piece (.inl j) (.inr (.inl l)) ↔
          curve j a ∈ left.piece l) ∧
        (∀ j r, FrontierCover.Incident piece (.inl j) (.inr (.inr r)) ↔
          curve j b ∈ right.piece r) := by
  refine ⟨RootBranches.finite_index f a b t₀ hproper hf hJac, ?_⟩
  obtain ⟨curve, hc, hroot, hcomplete, _⟩ := exists_arcs f a b t₀ hcont hproper hf hJac p hp hrel
  have hab := t₀.property.1.trans t₀.property.2
  refine ⟨curve, ?_, ?_, ?_, ?_⟩
  · exact SlabCover.cover _ curve
      (fun t ht x hx => (hcomplete ⟨t, ht⟩ x).mp hx |>.exists)
      left.piece right.piece left.cover right.cover
  · exact SlabCover.accessible _ hab curve hc hroot left.piece right.piece
      left.subset right.subset left.accessible right.accessible
  · exact SlabCover.incident_arc_left_iff _ hab curve hc hroot left.piece right.piece
      left.subset right.subset
  · exact SlabCover.incident_arc_right_iff _ hab curve hc hroot left.piece right.piece
      left.subset right.subset

end LeanCanny.Connectivity.RegularRootArcs

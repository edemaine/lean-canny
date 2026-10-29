/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.LocalProperRootBranches
public import LeanCanny.Geometry.RootSlabEquivalence
public import LeanCanny.Connectivity.RegularRootArcs
public import Mathlib.Topology.LocalAtTarget

/-! # Complete original root arcs from a regular auxiliary equation

Only the auxiliary equation needs invertible spatial derivatives on the open
slab. Properness, algebraic endpoint bounds, and endpoint roots come from the
original equations. Extra auxiliary roots at excluded endpoints are ignored.
-/

@[expose] public section
namespace LeanCanny.Connectivity.OriginalRootArcs
open Set Function Topology Geometry
variable {ι F G : Type*} [Fintype ι] [NormedAddCommGroup F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- All original roots on the slab have unique anchored branches. Their limits
satisfy the original equations even if the auxiliary endpoint fibers differ. -/
theorem exists_anchored_arcs (f : ℝ × (ι → ℝ) → F) (g : ℝ × (ι → ℝ) → G)
    (a b : ℝ) (t₀ : Ioo a b) (heq : ∀ t ∈ Ioo a b, ∀ x, f (t, x) = 0 ↔ g (t, x) = 0)
    (hcont : Continuous f) (hproper : IsProperMap (RootProjection.projection f))
    (hf : ∀ z : RootProjection.Space g, RootProjection.projection g z ∈ Ioo a b → ContDiffAt ℝ 1 g z.val)
    (hJac : ∀ z : RootProjection.Space g, RootProjection.projection g z ∈ Ioo a b →
      (fderiv ℝ g z.val ∘L ContinuousLinearMap.inr ℝ ℝ (ι → ℝ)).IsInvertible)
    (p : ι → Polynomial (Polynomial ℝ)) (hp : ∀ i, p i ≠ 0)
    (hrel : ∀ z : RootProjection.Space f, RootProjection.projection f z ∈ Ioo a b →
      ∀ i, AlgebraicBranchLimit.value (p i) z.val.1 (z.val.2 i) = 0) :
    Finite (RootBranches.Index g a b t₀) ∧
    ∃ curve : RootBranches.Index g a b t₀ → ℝ → ι → ℝ,
      (∀ j, curve j t₀.val = j.val.val.val.2) ∧
      (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
      (∀ j t, t ∈ Icc a b → f (t, curve j t) = 0) ∧
      (∀ t : Ioo a b, ∀ x, f (t.val, x) = 0 ↔ ∃! j, curve j t.val = x) ∧
      ∀ j, FrontierCover.Accessible ((fun t => (t, curve j t)) '' Ioo a b) := by
  classical
  have hab : a < b := t₀.property.1.trans t₀.property.2
  have hgproper : IsProperMap (RootBranches.projection g a b) :=
    RootSlabEquivalence.proper_restriction f g (Ioo a b) heq (hproper.restrictPreimage (Ioo a b))
  refine ⟨LocalProperRootBranches.finite_index g a b t₀ hgproper hf hJac, ?_⟩
  obtain ⟨branch, hanchor, hgroots, hgcomplete⟩ :=
    LocalProperRootBranches.exists_anchored_branches g a b t₀ hgproper hf hJac
  have hroots (j : RootBranches.Index g a b t₀) (t : Ioo a b) : f (t.val, branch j t) = 0 :=
    (heq t.val t.property (branch j t)).mpr (hgroots j t)
  have hcomplete (t : Ioo a b) (x : ι → ℝ) : f (t.val, x) = 0 ↔ ∃! j, branch j t = x :=
    (heq t.val t.property x).trans (hgcomplete t x)
  let K : ι → Set ℝ := fun i =>
    (fun z : RootProjection.Space f => z.val.2 i) '' (RootProjection.projection f ⁻¹' Icc a b)
  have hK (i : ι) : IsCompact (K i) :=
    (hproper.isCompact_preimage isCompact_Icc).image
      ((continuous_apply i).comp (continuous_snd.comp continuous_subtype_val))
  let total : RootBranches.Index g a b t₀ → ℝ → ι → ℝ := fun j t =>
    if ht : t ∈ Ioo a b then branch j ⟨t, ht⟩ else 0
  have htval (j : RootBranches.Index g a b t₀) (t : Ioo a b) : total j t.val = branch j t := by
    simp only [total, dite_eq_left t.property]
  have htcont (j : RootBranches.Index g a b t₀) : ContinuousOn (total j) (Ioo a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply (branch j).continuous.congr
    intro t
    exact (htval j t).symm
  have htbound (j : RootBranches.Index g a b t₀) (t : ℝ) (ht : t ∈ Ioo a b) (i : ι) :
      total j t i ∈ K i := by
    let z : RootProjection.Space f := ⟨(t, branch j ⟨t, ht⟩), hroots j ⟨t, ht⟩⟩
    refine ⟨z, Ioo_subset_Icc_self ht, ?_⟩
    rw [htval j ⟨t, ht⟩]
  have htzero (j : RootBranches.Index g a b t₀) (t : ℝ) (ht : t ∈ Ioo a b) (i : ι) :
      AlgebraicBranchLimit.value (p i) t (total j t i) = 0 := by
    rw [htval j ⟨t, ht⟩]
    exact hrel ⟨(t, branch j ⟨t, ht⟩), hroots j ⟨t, ht⟩⟩ ht i
  have hext (j : RootBranches.Index g a b t₀) := AlgebraicBranchLimit.continuous_extension
    hab (htcont j) p hp K hK (htbound j) (htzero j)
  choose curve hc heq using hext
  have hvalue (j : RootBranches.Index g a b t₀) (t : Ioo a b) : curve j t.val = branch j t :=
    (heq j t.property).trans (htval j t)
  have hfullroot (j : RootBranches.Index g a b t₀) (t : ℝ) (ht : t ∈ Icc a b) :
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

end LeanCanny.Connectivity.OriginalRootArcs

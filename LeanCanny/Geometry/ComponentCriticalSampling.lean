/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RegularFiber
public import LeanCanny.Geometry.ProjectionCriticalBranches
public import LeanCanny.Geometry.ProjectionCritical
public import Mathlib.Topology.Order.Compact
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Critical points sample every component of a compact regular level

Each component is compact and relatively open in a regular fiber. A projection
maximum on the component is therefore a local maximum on the entire level.
Lagrange multipliers place it in the actual spatial projection-critical
system. Local path connectivity gives a path to it from every point of that
component. This samples all components, rather than just one global maximum.
-/

@[expose] public section

namespace LeanCanny.Geometry.ComponentCriticalSampling
open Set Filter MvPolynomial
open scoped Topology
set_option backward.isDefEq.respectTransparency false

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every point of a compact regular level can reach a critical sample without
leaving its own level component. The projection direction is fixed in advance. -/
theorem exists_joined_critical (p : MvPolynomial ι ℝ) (base : ι) (v : ι → ℝ)
    (hv : v base = 1) (t : ℝ)
    (hcompact : IsCompact {x : ι → ℝ | p.eval x = t})
    (hregular : ∀ x : ι → ℝ, p.eval x = t →
      Function.Surjective (fderiv ℝ (fun y => p.eval y) x))
    (x : ι → ℝ) (hx : p.eval x = t) :
    ∃ y : ι → ℝ, JoinedIn {z | p.eval z = t} x y ∧
      PolynomialRootFamily.value (ProjectionCriticalBranches.equation p base v) (t, y) = 0 := by
  let g : (ι → ℝ) → ℝ := fun y => p.eval y
  let L := RegularFiber.Fiber g t
  have hsmooth : ContDiff ℝ 1 g :=
    (ProjectionCritical.contDiff_eval (RingHom.id ℝ) p).of_le le_top
  let : LocallyPathConnectedSpace L := RegularFiber.locallyPathConnected g t
    (fun _ => hsmooth.contDiffAt) (fun z => hregular z.val z.property)
  let : CompactSpace L := isCompact_iff_compactSpace.mp hcompact
  let x' : L := ⟨x, hx⟩
  have hC : IsCompact (connectedComponent x') := isClosed_connectedComponent.isCompact
  have hobj : Continuous (fun z : L => ProjectionCritical.projection v z.val) :=
    (ProjectionCritical.projection v).continuous.comp continuous_subtype_val
  obtain ⟨y, hy, hmax⟩ := hC.exists_isMaxOn ⟨x', mem_connectedComponent⟩ hobj.continuousOn
  have hlocal : IsLocalMaxOn (ProjectionCritical.projection v) {z | p.eval z = t} y.val := by
    change ∀ᶠ z in 𝓝[{z | p.eval z = t}] y.val,
      ProjectionCritical.projection v z ≤ ProjectionCritical.projection v y.val
    rw [← map_nhds_subtype_val (s := {z | p.eval z = t}) y]
    exact hmax.isLocalMax (isOpen_connectedComponent.mem_nhds hy)
  have hlocal' : IsLocalMaxOn (ProjectionCritical.projection v) {z | g z = g y.val} y.val := by
    simpa only [y.property] using hlocal
  obtain ⟨Λ, hΛ⟩ := ActiveExtremum.exists_normalized g (ProjectionCritical.projection v) y.val
    _ _ hlocal' (hsmooth.contDiffAt.hasStrictFDerivAt one_ne_zero)
    (ProjectionCritical.projection v).hasStrictFDerivAt (hregular y.val y.property)
  have hscalar (i : ι) : v i = Λ 1 * (pderiv i p).eval y.val := by
    have he := hΛ (Pi.single i 1)
    rw [ProjectionCritical.projection_single] at he
    change v i = Λ ((fderiv ℝ (fun z => p.eval₂ (RingHom.id ℝ) z) y.val) (Pi.single i 1)) at he
    rw [PolynomialCalculus.fderiv_eq,
      PolynomialCalculus.derivative_single] at he
    have hmul (r : ℝ) : Λ r = Λ 1 * r := by
      simpa only [smul_eq_mul, mul_one, mul_comm] using Λ.map_smul r 1
    exact he.trans (hmul _)
  have hpartial (i : ι) : (pderiv i p).eval y.val = v i * (pderiv base p).eval y.val := by
    have hbase : Λ 1 * (pderiv base p).eval y.val = 1 := (hscalar base).symm.trans hv
    calc
      _ = (pderiv i p).eval y.val * (Λ 1 * (pderiv base p).eval y.val) := by rw [hbase, mul_one]
      _ = (Λ 1 * (pderiv i p).eval y.val) * (pderiv base p).eval y.val := by ring
      _ = _ := by rw [← hscalar i]
  have hj : Joined x' y := by
    apply mem_pathComponent_iff.mp
    rwa [pathComponent_eq_connectedComponent]
  have hj' := (joinedIn_univ.mpr hj).map continuous_subtype_val.continuousOn
  refine ⟨y.val, hj'.mono ?_, (ProjectionCriticalBranches.value_iff p base v hv t y.val).mpr
    ⟨y.property, hpartial⟩⟩
  rintro z ⟨w, _, rfl⟩
  exact w.property

abbrev Samples (p : MvPolynomial ι ℝ) (base : ι) (v : ι → ℝ) (t : ℝ) :=
  {x : ι → ℝ // PolynomialRootFamily.value (ProjectionCriticalBranches.equation p base v) (t, x) = 0}

noncomputable def componentMap (p : MvPolynomial ι ℝ) (base : ι) (v : ι → ℝ)
    (hv : v base = 1) (t : ℝ) : Samples p base v t →
      ConnectedComponents (RegularFiber.Fiber (fun x => p.eval x) t) := fun z =>
  ConnectedComponents.mk ⟨z.val, ((ProjectionCriticalBranches.value_iff p base v hv t z.val).mp z.property).1⟩

/-- The map from actual polynomial critical roots onto fiber components is
surjective. Multiple samples in a component are permitted. -/
theorem componentMap_surjective (p : MvPolynomial ι ℝ) (base : ι) (v : ι → ℝ)
    (hv : v base = 1) (t : ℝ)
    (hcompact : IsCompact {x : ι → ℝ | p.eval x = t})
    (hregular : ∀ x : ι → ℝ, p.eval x = t →
      Function.Surjective (fderiv ℝ (fun y => p.eval y) x)) :
    Function.Surjective (componentMap p base v hv t) := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨y, hjoined, hroot⟩ := exists_joined_critical p base v hv t hcompact hregular x.val x.property
  let z : Samples p base v t := ⟨y, hroot⟩
  let y' : RegularFiber.Fiber (fun x => p.eval x) t :=
    ⟨y, ((ProjectionCriticalBranches.value_iff p base v hv t y).mp hroot).1⟩
  refine ⟨z, ?_⟩
  change ConnectedComponents.mk y' = ConnectedComponents.mk x
  apply ConnectedComponents.coe_eq_coe'.mpr
  apply pathComponent_subset_component x
  have hind : Topology.IsInducing
      (Subtype.val : RegularFiber.Fiber (fun x => p.eval x) t → (ι → ℝ)) := by
    exact Topology.IsEmbedding.subtypeVal.isInducing
  have hj : JoinedIn univ x y' :=
    (hind.joinedIn_image (F := univ) (x := x) (y := y') (mem_univ x) (mem_univ y')).mp
      (by simpa only [image_univ, Subtype.range_val_subtype] using hjoined)
  exact hj.joined

/-- Any finite algebraic bound on the critical roots bounds the number of
components as well. Finiteness is charged to the actual sample set. -/
theorem card_components_le (p : MvPolynomial ι ℝ) (base : ι) (v : ι → ℝ)
    (hv : v base = 1) (t : ℝ) [Finite (Samples p base v t)]
    (hcompact : IsCompact {x : ι → ℝ | p.eval x = t})
    (hregular : ∀ x : ι → ℝ, p.eval x = t →
      Function.Surjective (fderiv ℝ (fun y => p.eval y) x)) :
    Nat.card (ConnectedComponents (RegularFiber.Fiber (fun x => p.eval x) t)) ≤
      Nat.card (Samples p base v t) :=
  Nat.card_le_card_of_surjective _ (componentMap_surjective p base v hv t hcompact hregular)

/-- Avoiding a critical-value annihilator makes the entire hypersurface level
regular, rather than just the points selected by a projection system. -/
theorem regular_level_of_annihilator (p : MvPolynomial ι ℝ) (c : Polynomial ℝ)
    (hc : Polynomial.aeval p c ∈ (Algebra.CriticalValueAnnihilator.gradientIdeal p).radical)
    (t : ℝ) (ht : c.eval t ≠ 0) (x : ι → ℝ) (hx : p.eval x = t) :
    Function.Surjective (fderiv ℝ (fun y => p.eval y) x) := by
  have hne : fderiv ℝ (fun y => p.eval y) x ≠ 0 := by
    intro hz
    have hgrad := (PolynomialCalculus.critical_iff (RingHom.id ℝ) p x).mp hz
    have he := Algebra.CriticalValueAnnihilator.eval_annihilator p c hc x (by
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hgrad)
    have hpval : aeval x p = t := by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hx
    rw [hpval] at he
    exact ht he
  exact surjective_of_ne_zero_of_finrank_eq_one (K := ℝ)
    (by simp) (fun h => hne (ContinuousLinearMap.coe_injective h))

/-- For a proper polynomial, one constructed integer direction gives a finite
critical sample set surjecting onto every component of every retained level.
The excluded levels are the roots of a single nonzero polynomial. -/
theorem exists_finite_component_sampler (p : MvPolynomial ι ℝ) (base : ι)
    (hp : IsProperMap (fun x : ι → ℝ => p.eval x)) :
    ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex base → ℕ,
      ∃ r : Polynomial ℝ, r ≠ 0 ∧ {t : ℝ | r.eval t = 0}.Finite ∧
        let v := Algebra.ProjectionFiniteSpecialization.normalizedDirection base (fun i => (u i : ℝ))
        ∀ t, r.eval t ≠ 0 → Finite (Samples p base v t) ∧
          Function.Surjective (componentMap p base v
            (by simp [v, Algebra.ProjectionFiniteSpecialization.normalizedDirection]) t) := by
  obtain ⟨u, r, hr, _, hnative⟩ := ProjectionCriticalBranches.exists_regular_direction p base
  obtain ⟨c, hc, hcm⟩ := Algebra.CriticalValueAnnihilator.exists_annihilator p
  refine ⟨u, r * c, mul_ne_zero hr hc, Polynomial.finite_setOfPred_isRoot (mul_ne_zero hr hc), ?_⟩
  let v := Algebra.ProjectionFiniteSpecialization.normalizedDirection base (fun i => (u i : ℝ))
  have hv : v base = 1 := by simp [v, Algebra.ProjectionFiniteSpecialization.normalizedDirection]
  let f := PolynomialRootFamily.value (ProjectionCriticalBranches.equation p base v)
  have hproper : IsProperMap (RootProjection.projection f) := ProjectionCriticalBranches.isProperMap p base v hv hp
  dsimp only
  intro t ht
  have hfac : r.eval t ≠ 0 ∧ c.eval t ≠ 0 := mul_ne_zero_iff.mp (by simpa only [Polynomial.eval_mul] using ht)
  have hcompact : IsCompact {x : ι → ℝ | p.eval x = t} :=
    hp.isCompact_preimage isCompact_singleton
  have hregular := regular_level_of_annihilator p c hcm t hfac.2
  have hfin := RootProjection.finite_fiber f t hproper
    (fun z _ => (PolynomialRootFamily.contDiff_value _ 1).contDiffAt)
    (fun z hz => (PolynomialRootFamily.isInvertible_iff _ z.val).mpr
      (hnative z.val.1 z.val.2 (by
        change r.eval (RootProjection.projection f z) ≠ 0
        rw [hz]
        exact hfac.1) z.property))
  let enc : Samples p base v t → (RootProjection.projection f ⁻¹' {t}) :=
    fun z => ⟨⟨(t, z.val), z.property⟩, rfl⟩
  let : Finite (RootProjection.projection f ⁻¹' {t}) := hfin.to_subtype
  have hfinite : Finite (Samples p base v t) := Finite.of_injective enc (by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : (RootProjection.projection f ⁻¹' {t}) => z.val.val.2) hab)
  exact ⟨hfinite, componentMap_surjective p base v hv t hcompact hregular⟩

end LeanCanny.Geometry.ComponentCriticalSampling

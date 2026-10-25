/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Topology.Connected.LocallyPathConnected

/-! # Local path connectivity of regular fibers

Restricting an implicit-function chart to a level set gives an actual local
homeomorphism to the derivative's kernel. Its model is a real normed space,
so regular fibers are locally path connected. The kernel, and therefore the
chart model, may vary with the point of the fiber.
-/

@[expose] public section

namespace LeanCanny.Geometry.RegularFiber
open Set Filter Topology
open scoped Topology

abbrev Fiber {E F : Type*} (f : E → F) (c : F) := {x : E // f x = c}

section Restriction
variable {X F G : Type*} [TopologicalSpace X] [TopologicalSpace F] [TopologicalSpace G]

/-- Restrict a local product chart whose first coordinate is the level map.
Only the fiber is retained; the resulting target is open in the free model. -/
noncomputable def restrictFiber (e : OpenPartialHomeomorph X (F × G))
    (f : X → F) (c : F) (a : Fiber f c)
    (hfirst : ∀ x ∈ e.source, (e x).1 = f x) :
    OpenPartialHomeomorph (Fiber f c) G := by
  classical
  let V : Set G := {y | (c, y) ∈ e.target}
  have hroot (y : G) (hy : y ∈ V) : f (e.symm (c, y)) = c := by
    exact (hfirst _ (e.map_target hy)).symm.trans (congrArg Prod.fst (e.right_inv hy))
  let inv : G → Fiber f c := fun y => if hy : y ∈ V then ⟨e.symm (c, y), hroot y hy⟩ else a
  have hinv : ContinuousOn inv V := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hcont : Continuous (fun y : V => e.symm (c, y.val)) :=
      e.continuousOn_symm.comp_continuous (continuous_const.prodMk continuous_subtype_val)
        (fun y => y.property)
    have hsub : Continuous (fun y : V => (⟨e.symm (c, y.val), hroot y.val y.property⟩ : Fiber f c)) :=
      hcont.subtype_mk _
    apply hsub.congr
    intro y
    change (⟨e.symm (c, y.val), hroot y.val y.property⟩ : Fiber f c) = inv y.val
    simp only [inv, dite_eq_left y.property]
  refine {
    toFun := fun x => (e x.val).2
    invFun := inv
    source := Subtype.val ⁻¹' e.source
    target := V
    map_source' := ?_
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    open_source := e.open_source.preimage continuous_subtype_val
    open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
    continuousOn_toFun := continuous_snd.continuousOn.comp
      (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx))
      (fun _ _ => mem_univ _)
    continuousOn_invFun := hinv }
  · intro x hx
    have hxfirst : (e x.val).1 = c := (hfirst _ hx).trans x.property
    have heq : (c, (e x.val).2) = e x.val := Prod.ext hxfirst.symm rfl
    change (c, (e x.val).2) ∈ e.target
    rw [heq]
    exact e.map_source hx
  · intro y hy
    change (inv y).val ∈ e.source
    simpa only [inv, dite_eq_left hy] using e.map_target hy
  · intro x hx
    have hxfirst : (e x.val).1 = c := (hfirst _ hx).trans x.property
    have heq : (c, (e x.val).2) = e x.val := Prod.ext hxfirst.symm rfl
    have hy : (e x.val).2 ∈ V := by
      change (c, (e x.val).2) ∈ e.target
      rw [heq]
      exact e.map_source hx
    apply Subtype.ext
    simp only [inv, dite_eq_left hy, heq, e.left_inv hx]
  · intro y hy
    simp only [inv, dite_eq_left hy, e.right_inv hy]

@[simp] theorem restrictFiber_source (e : OpenPartialHomeomorph X (F × G))
    (f : X → F) (c : F) (a : Fiber f c)
    (hfirst : ∀ x ∈ e.source, (e x).1 = f x) :
    (restrictFiber e f c a hfirst).source = Subtype.val ⁻¹' e.source := rfl

end Restriction

section Locality
variable {X : Type*} [TopologicalSpace X] {G : X → Type*}
  [∀ x, TopologicalSpace (G x)] [∀ x, LocallyPathConnectedSpace (G x)]

/-- Local path connectivity can be checked using point-dependent chart models. -/
theorem locallyPathConnected_of_charts (chart : ∀ x, OpenPartialHomeomorph X (G x))
    (hchart : ∀ x, x ∈ (chart x).source) : LocallyPathConnectedSpace X := by
  constructor
  intro x
  rw [hasBasis_self]
  intro s hs
  let e := chart x
  let : LocallyPathConnectedSpace e.target := e.open_target.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace e.source :=
    e.toHomeomorphSourceTarget.symm.locallyPathConnectedSpace
  let x' : e.source := ⟨x, hchart x⟩
  have hpre : Subtype.val ⁻¹' s ∈ 𝓝 x' := continuous_subtype_val.continuousAt.preimage_mem_nhds hs
  obtain ⟨u, ⟨hu, hpath⟩, hus⟩ := (path_connected_basis x').mem_iff.mp hpre
  refine ⟨Subtype.val '' u, ?_, hpath.image continuous_subtype_val, ?_⟩
  · exact e.open_source.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hu
  · rintro z ⟨y, hy, rfl⟩
    exact hus hy

end Locality

section Implicit
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- An implicit-function chart gives coordinates for the entire local fiber. -/
noncomputable def chart (f : E → F) (c : F) (a : Fiber f c) (D : E →L[ℝ] F)
    (hf : HasStrictFDerivAt f D a.val) (hD : Function.Surjective D) :
    OpenPartialHomeomorph (Fiber f c) D.ker :=
  restrictFiber (hf.implicitToOpenPartialHomeomorph f D (LinearMap.range_eq_top.mpr hD))
    f c a (fun _ _ => hf.implicitToOpenPartialHomeomorph_fst _ _)

theorem mem_chart_source (f : E → F) (c : F) (a : Fiber f c) (D : E →L[ℝ] F)
    (hf : HasStrictFDerivAt f D a.val) (hD : Function.Surjective D) :
    a ∈ (chart f c a D hf hD).source :=
  hf.mem_implicitToOpenPartialHomeomorph_source _

/-- No connectedness or compactness of the fiber is assumed. -/
theorem locallyPathConnected (f : E → F) (c : F)
    (hf : ∀ x : Fiber f c, ContDiffAt ℝ 1 f x.val)
    (hD : ∀ x : Fiber f c, Function.Surjective (fderiv ℝ f x.val)) :
    LocallyPathConnectedSpace (Fiber f c) := by
  let charts (x : Fiber f c) := chart f c x (fderiv ℝ f x.val)
    ((hf x).hasStrictFDerivAt one_ne_zero) (hD x)
  exact locallyPathConnected_of_charts charts
    (fun x => mem_chart_source f c x _ ((hf x).hasStrictFDerivAt one_ne_zero) (hD x))

theorem joined_iff_component_eq (f : E → F) (c : F)
    (hf : ∀ x : Fiber f c, ContDiffAt ℝ 1 f x.val)
    (hD : ∀ x : Fiber f c, Function.Surjective (fderiv ℝ f x.val)) (x y : Fiber f c) :
    Joined x y ↔ ConnectedComponents.mk x = ConnectedComponents.mk y := by
  let : LocallyPathConnectedSpace (Fiber f c) := locallyPathConnected f c hf hD
  exact (ConnectedComponents.coe_eq_coe.trans (connectedComponent_eq_iff_joined x y)).symm

/-- Compact regular fibers have finitely many components, each of which is
also a path component. This includes empty fibers. -/
theorem finite_components (f : E → F) (c : F)
    (hf : ∀ x : Fiber f c, ContDiffAt ℝ 1 f x.val)
    (hD : ∀ x : Fiber f c, Function.Surjective (fderiv ℝ f x.val))
    (hcompact : IsCompact {x : E | f x = c}) :
    Finite (ConnectedComponents (Fiber f c)) := by
  let : LocallyPathConnectedSpace (Fiber f c) := locallyPathConnected f c hf hD
  let : CompactSpace (Fiber f c) := isCompact_iff_compactSpace.mp hcompact
  infer_instance

end Implicit
end LeanCanny.Geometry.RegularFiber

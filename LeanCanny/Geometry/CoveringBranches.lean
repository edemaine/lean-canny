/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-! # Complete global branches of a finite covering

Over a simply connected, locally path-connected base, local branches of a
covering glue to global branches indexed by a single fiber. Every point of
every fiber lies on exactly one branch. When that indexing fiber is finite,
the branches form a finite closed path cover of the total space.

For a regular algebraic curve, the map to use is projection to a parameter
interval. The covering property must be proved from the root equations and
properness; this file does not assume a global enumeration of curve branches.
-/

@[expose] public section

namespace LeanCanny.Geometry.CoveringBranches
open Set Function Topology

variable {A E : Type*} [TopologicalSpace A] [TopologicalSpace E]

/-- A covering over a simply connected base has a complete set of global
branches, indexed by one fiber. No finiteness hypothesis is needed yet. -/
theorem exists_branches [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    {p : E → A} (hp : IsCoveringMap p) (a₀ : A) :
    ∃ branch : (p ⁻¹' {a₀}) → C(A, E),
      (∀ i, branch i a₀ = i.val) ∧
      (∀ i a, p (branch i a) = a) ∧
      ∀ a e, p e = a → ∃! i, branch i a = e := by
  classical
  have hLift (i : p ⁻¹' {a₀}) :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id A) a₀ i.val i.property
  choose branch hs huniq using hLift
  refine ⟨branch, fun i => (hs i).1, ?_, ?_⟩
  · intro i a
    exact congrFun (hs i).2 a
  · intro a e he
    obtain ⟨g, ⟨hg₀, hg⟩, hguniq⟩ :=
      hp.existsUnique_continuousMap_lifts (ContinuousMap.id A) a e he
    let i : p ⁻¹' {a₀} := ⟨g a₀, congrFun hg a₀⟩
    have hgi : g = branch i := huniq i g ⟨rfl, hg⟩
    refine ⟨i, ?_, ?_⟩
    · exact (congrArg (fun h : C(A, E) => h a) hgi).symm.trans hg₀
    · intro j hj
      have hjg : branch j = g := hguniq (branch j) ⟨hj, (hs j).2⟩
      apply Subtype.ext
      exact ((hs j).1.symm.trans (congrArg (fun h : C(A, E) => h a₀) hjg))

/-- The branch enumeration identifies all fibers, so a finite indexing fiber
gives finite fibers throughout the regular interval. -/
theorem finite_fiber [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    {p : E → A} (hp : IsCoveringMap p) (a₀ : A) [Finite (p ⁻¹' {a₀})] (a : A) :
    Finite (p ⁻¹' {a}) := by
  obtain ⟨branch, _, hproj, hcover⟩ := exists_branches hp a₀
  let f : (p ⁻¹' {a₀}) → (p ⁻¹' {a}) := fun i => ⟨branch i a, hproj i a⟩
  apply Finite.of_surjective f
  intro e
  obtain ⟨i, hi, _⟩ := hcover a e.val e.property
  exact ⟨i, Subtype.ext hi⟩

/-- A section has closed image in a Hausdorff total space: its image is the
equalizer of `branch ∘ p` and the identity. -/
theorem isClosed_range_of_section [T2Space E] {p : E → A} (hp : Continuous p)
    (branch : C(A, E)) (hproj : ∀ a, p (branch a) = a) : IsClosed (range branch) := by
  have heq : range branch = {e | branch (p e) = e} := by
    ext e
    constructor
    · rintro ⟨a, rfl⟩
      change branch (p (branch a)) = branch a
      rw [hproj]
    · intro h
      exact ⟨p e, h⟩
  rw [heq]
  exact isClosed_eq (branch.continuous.comp hp) continuous_id

/-- A covering of a simply connected base decomposes into disjoint
closed, path-connected branches. -/
theorem exists_closed_path_cover [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    [T2Space E] {p : E → A} (hp : IsCoveringMap p) (a₀ : A) :
    ∃ branch : (p ⁻¹' {a₀}) → C(A, E),
      (∀ i a, p (branch i a) = a) ∧
      (∀ e, ∃! i, e ∈ range (branch i)) ∧
      (∀ i, IsClosed (range (branch i))) ∧
      ∀ i, ∀ x ∈ range (branch i), ∀ y ∈ range (branch i),
        JoinedIn (range (branch i)) x y := by
  obtain ⟨branch, _, hproj, hcover⟩ := exists_branches hp a₀
  refine ⟨branch, hproj, ?_, ?_, ?_⟩
  · intro e
    obtain ⟨i, hi, huniq⟩ := hcover (p e) e rfl
    refine ⟨i, ⟨p e, hi⟩, ?_⟩
    rintro j ⟨a, ha⟩
    have he : a = p e := (hproj j a).symm.trans (congrArg p ha)
    apply huniq
    rwa [← he]
  · intro i
    exact isClosed_range_of_section hp.continuous (branch i) (hproj i)
  · intro i x hx y hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have hpath : JoinedIn (univ : Set A) a b := joinedIn_univ.mpr (PathConnectedSpace.joined a b)
    simpa only [image_univ] using hpath.map (branch i).continuous.continuousOn

/-- Open real parameter intervals meet the hypotheses for global branches. -/
theorem exists_interval_branches {a b : ℝ} {p : E → Ioo a b}
    (hp : IsCoveringMap p) (t₀ : Ioo a b) :
    ∃ branch : (p ⁻¹' {t₀}) → C(Ioo a b, E),
      (∀ i, branch i t₀ = i.val) ∧
      (∀ i t, p (branch i t) = t) ∧
      ∀ t e, p e = t → ∃! i, branch i t = e := by
  let : ContractibleSpace (Ioo a b) :=
    (convex_Ioo a b).contractibleSpace ⟨t₀.val, t₀.property⟩
  let : LocallyPathConnectedSpace (Ioo a b) := isOpen_Ioo.locallyPathConnectedSpace
  exact exists_branches hp t₀

end LeanCanny.Geometry.CoveringBranches

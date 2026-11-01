/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedGridArcs
public import LeanCanny.Connectivity.AlgebraicArcFilter
/-! # Exact anchored critical arcs over one selected old algebra component

Validated relative squarefree factors make the actual coordinate grid
regular. Actual selected Gram trailing factors prune its extra coordinate
combinations. Every retained endpoint still satisfies the original rows.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedCriticalArcs
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry IntegralMixedSelectedGridArcs
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

abbrev Fiber (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) :=
  {z : Free r → ℝ // original x hm r φ (t,z) = 0}

theorem anchored_arcs (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (choice : Free r → Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r))
    (hc : ∀ j, IntegralMixedCoordinateSquarefree.Valid x hm r j φ (choice j))
    (valueChoice : Free r → Fin (IntegralMixedValueTrailing.ChoiceBound P r))
    (hv : ∀ j, IntegralMixedValueTrailing.Valid x hm r j φ (valueChoice j))
    (a b : ℝ) (t₀ : Ioo a b)
    (havoid : ∀ t ∈ Ioo a b, ∀ j,
      (IntegralMixedCoordinateSquarefree.exceptional x hm r j (choice j)).eval₂ φ.toRingHom t ≠ 0)
    (hvalue : ∀ t ∈ Ioo a b, ∀ j,
      (IntegralMixedValueTrailing.factor x hm r j (valueChoice j)).eval₂ φ.toRingHom t ≠ 0) :
    Finite (Fiber x hm r φ t₀.val) ∧
    ∃ curve : Fiber x hm r φ t₀.val → ℝ → Free r → ℝ,
      (∀ j, curve j t₀.val = j.val) ∧
      (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
      (∀ j t, t ∈ Icc a b → original x hm r φ (t,curve j t) = 0) ∧
      (∀ t : Ioo a b, ∀ z, original x hm r φ (t.val,z) = 0 ↔ ∃! j, curve j t.val = z) ∧
      ∀ j, FrontierCover.Accessible ((fun t => (t,curve j t)) '' Ioo a b) := by
  obtain ⟨hfinite, branch, _, hcont, hgrid, hcomplete, _⟩ :=
    IntegralMixedSelectedGridArcs.anchored_arcs x hm r φ choice hc a b t₀ havoid
  let I := RootBranches.Index (regularGrid x hm r φ choice) a b t₀
  let : Finite I := hfinite
  let Q := fun j => IntegralMixedValueTrailing.selectedValue x hm r j φ
  have Hrel (i : I) (j : Free r) (t : ℝ) (ht : t ∈ Ioo a b) :
      (Q j).eval₂ (Polynomial.evalRingHom t) (original x hm r φ (t,branch i t) j) = 0 := by
    rw [original_apply]
    apply IntegralMixedGridValue.root x hm r j φ t (branch i t)
    intro k
    have H := congrFun (hgrid i t (Ioo_subset_Icc_self ht)) k
    simpa only [grid, UnivariateRootFamily.value_diagonal, Pi.zero_apply] using H
  have Htrail (j : Free r) (t : ℝ) (ht : t ∈ Ioo a b) : (Q j).trailingCoeff.eval t ≠ 0 := by
    rw [← IntegralMixedValueTrailing.factor_specialization x hm r j φ (valueChoice j) (hv j), Polynomial.eval_map]
    exact hvalue t ht j
  have Hcover (t : Ioo a b) (z : Free r → ℝ) (hz : original x hm r φ (t.val,z) = 0) :
      ∃! i : I, branch i t.val = z := by
    apply (hcomplete t z).mp
    funext j
    rw [grid, UnivariateRootFamily.value_diagonal]
    exact capture x hm r φ t.val z hz j
  obtain ⟨Hcont, Hroot, Hcomplete, Haccess⟩ := AlgebraicArcFilter.filtered_arcs
    (original x hm r φ) (PolynomialRootFamily.contDiff_value _ 1).continuous
    a b t₀ branch hcont Hcover Q Hrel Htrail
  let J := AlgebraicArcFilter.Label (original x hm r φ) branch t₀.val
  let : Finite J := Finite.of_injective (fun j : J => (j.val : I)) (fun _ _ h => Subtype.ext h)
  let point : J → Fiber x hm r φ t₀.val := fun j =>
    ⟨branch j.val t₀.val, Hroot j t₀.val (Ioo_subset_Icc_self t₀.property)⟩
  have Hbij : Function.Bijective point := by
    constructor
    · intro j k Hjk
      obtain ⟨i, _, Huniq⟩ := (Hcomplete t₀ (branch j.val t₀.val)).mp
        (Hroot j t₀.val (Ioo_subset_Icc_self t₀.property))
      exact (Huniq j rfl).trans (Huniq k (congrArg Subtype.val Hjk).symm).symm
    · intro z
      obtain ⟨j, Hj, _⟩ := (Hcomplete t₀ z.val).mp z.property
      exact ⟨j, Subtype.ext Hj⟩
  let e : J ≃ Fiber x hm r φ t₀.val := Equiv.ofBijective point Hbij
  refine ⟨Finite.of_surjective point Hbij.surjective, fun j => branch (e.symm j).val, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact congrArg Subtype.val (e.apply_symm_apply j)
  · intro j
    exact Hcont (e.symm j)
  · intro j t ht
    exact Hroot (e.symm j) t ht
  · intro t z
    constructor
    · intro hz
      obtain ⟨j, Hj, Huniq⟩ := (Hcomplete t z).mp hz
      refine ⟨e j, ?_, ?_⟩
      · simpa only [e.symm_apply_apply] using Hj
      · intro k Hk
        have H := congrArg e (Huniq (e.symm k) Hk)
        simpa only [e.apply_symm_apply] using H
    · rintro ⟨j, Hj, _⟩
      rw [← Hj]
      exact Hroot (e.symm j) t.val (Ioo_subset_Icc_self t.property)
  · intro j
    exact Haccess (e.symm j)

end LeanCanny.Connectivity.IntegralMixedSelectedCriticalArcs

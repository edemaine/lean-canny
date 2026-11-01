/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedGeometry
public import LeanCanny.Connectivity.OriginalRootArcs
/-! # Complete anchored arcs of the actual selected-parent coordinate grid -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedGridArcs
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def auxiliary (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (choice : Free r → Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r)) (j : Free r) :=
  (IntegralMixedCoordinateSquarefree.auxiliary x hm r j (choice j)).map (Polynomial.mapRingHom φ.toRingHom)

noncomputable def grid (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :=
  PolynomialRootFamily.value (UnivariateRootFamily.diagonal (fun j => selected x hm r j φ))

noncomputable def regularGrid (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (choice : Free r → Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r)) :=
  PolynomialRootFamily.value (UnivariateRootFamily.diagonal (auxiliary x hm r φ choice))

theorem regular_roots (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (choice : Free r → Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r))
    (hc : ∀ j, IntegralMixedCoordinateSquarefree.Valid x hm r j φ (choice j)) (t : ℝ) (z : Free r → ℝ)
    (ht : ∀ j, (IntegralMixedCoordinateSquarefree.exceptional x hm r j (choice j)).eval₂ φ.toRingHom t ≠ 0) :
    grid x hm r φ (t,z) = 0 ↔ regularGrid x hm r φ choice (t,z) = 0 := by
  have H (j : Free r) : (auxiliary x hm r φ choice j).eval₂ (Polynomial.evalRingHom t) (z j) = 0 ↔
      (selected x hm r j φ).eval₂ (Polynomial.evalRingHom t) (z j) = 0 := by
    rw [auxiliary, Polynomial.eval₂_map]
    exact IntegralMixedCoordinateSquarefree.roots_away x hm r j φ (choice j) (hc j) t (z j) (ht j)
  constructor <;> intro HZ <;> funext j
  · rw [regularGrid, UnivariateRootFamily.value_diagonal, Pi.zero_apply]
    apply (H j).mpr
    simpa only [grid, UnivariateRootFamily.value_diagonal, Pi.zero_apply] using congrFun HZ j
  · rw [grid, UnivariateRootFamily.value_diagonal, Pi.zero_apply]
    apply (H j).mp
    simpa only [regularGrid, UnivariateRootFamily.value_diagonal, Pi.zero_apply] using congrFun HZ j

theorem anchored_arcs (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (choice : Free r → Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r))
    (hc : ∀ j, IntegralMixedCoordinateSquarefree.Valid x hm r j φ (choice j))
    (a b : ℝ) (t₀ : Ioo a b)
    (ht : ∀ t ∈ Ioo a b, ∀ j, (IntegralMixedCoordinateSquarefree.exceptional x hm r j (choice j)).eval₂ φ.toRingHom t ≠ 0) :
    Finite (RootBranches.Index (regularGrid x hm r φ choice) a b t₀) ∧
    ∃ curve : RootBranches.Index (regularGrid x hm r φ choice) a b t₀ → ℝ → Free r → ℝ,
      (∀ j, curve j t₀.val = j.val.val.val.2) ∧
      (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
      (∀ j t, t ∈ Icc a b → grid x hm r φ (t, curve j t) = 0) ∧
      (∀ t : Ioo a b, ∀ z, grid x hm r φ (t.val,z) = 0 ↔ ∃! j, curve j t.val = z) ∧
      ∀ j, FrontierCover.Accessible ((fun t => (t,curve j t)) '' Ioo a b) := by
  apply OriginalRootArcs.exists_anchored_arcs (grid x hm r φ) (regularGrid x hm r φ choice) a b t₀
    (p := fun j => Polynomial.Bivariate.swap (selected x hm r j φ))
  · intro t ht' z
    exact regular_roots x hm r φ choice hc t z (ht t ht')
  · exact (PolynomialRootFamily.contDiff_value _ 1).continuous
  · exact IntegralMixedSelectedGeometry.proper x hm r φ
  · intro z _
    exact (PolynomialRootFamily.contDiff_value _ 1).contDiffAt
  · intro z hz
    apply UnivariateRootFamily.regular_diagonal _ z.val.1 z.val.2 _ z.property
    intro j
    rw [auxiliary, Polynomial.map_map]
    exact IntegralMixedCoordinateSquarefree.separable_away x hm r j φ (choice j) (hc j) z.val.1 (ht _ hz j)
  · intro j HZ
    exact selected_ne_zero x hm r j φ (Polynomial.Bivariate.swap.injective (HZ.trans (map_zero _).symm))
  · intro z _ j
    have H := congrFun z.property j
    change PolynomialRootFamily.value (UnivariateRootFamily.diagonal (fun j => selected x hm r j φ)) (z.val.1,z.val.2) j = 0 at H
    rw [UnivariateRootFamily.value_diagonal] at H
    have HE := Polynomial.Bivariate.aevalAeval_swap (z.val.2 j) z.val.1 (selected x hm r j φ)
    simp only [Polynomial.coe_aevalAeval_eq_evalEval] at HE
    unfold AlgebraicBranchLimit.value
    rw [Polynomial.eval₂_evalRingHom, HE, ← Polynomial.eval₂_evalRingHom]
    exact H

end LeanCanny.Connectivity.IntegralMixedSelectedGridArcs

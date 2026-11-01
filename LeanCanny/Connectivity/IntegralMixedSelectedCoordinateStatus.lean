/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedSlabCover
/-! # Selected coordinate cuts preserve zero status on actual physical arcs

Nonvanishing is transferred from the actual anchor on the same selected
parent component, rather than from a root of an absolute norm polynomial.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedCoordinateStatus
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry IntegralMixedSelectedCriticalArcs
open IntegralMixedSelectedCriticalCuts IntegralMixedSelectedPhysicalFiber
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem source_zero (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) (y : Fin (n+1) → ℝ)
    (hy : y ∈ physical x hm r φ t) :
    (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y = 0 := by
  have H := hy.2 (objective r)
  simpa only [IntegralMixedSweepRows.integerRow, ite_true] using H

theorem gradient_zero (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) (y : Fin (n+1) → ℝ)
    (hy : y ∈ physical x hm r φ t) (j : Free r) (hj : j ≠ objective r) :
    (MvPolynomial.pderiv (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j)
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) y = 0 := by
  simpa only [IntegralMixedSweepRows.integerRow, ite_eq_right hj] using hy.2 j

theorem zero_iff (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : IntegralMixedRelativeCuts.Choices x hm r φ)
    (a b : ℝ) (curve : ℝ → Fin (n+1) → ℝ) (hc : ContinuousOn curve (Icc a b))
    (hr : ∀ t ∈ Ioo a b, curve t ∈ physical x hm r φ t)
    (havoid : ∀ t ∈ Ioo a b, t ∉ bad x hm r φ c) (s t : Ioo a b) (j : Free r) :
    curve s.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j) = 0 ↔
      curve t.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j) = 0 := by
  let : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  apply IntegralMixedCoordinateTrailing.zero_iff x hm r j φ (c.coordinateIndex j) (c.coordinateValid j)
    (fun u : Ioo a b => u.val) (fun u : Ioo a b => curve u.val) continuous_subtype_val
    (continuousOn_iff_continuous_domRestrict.mp (hc.mono Ioo_subset_Icc_self))
  · intro u i hi
    exact (hr u.val u.property).1 i hi
  · intro u
    exact source_zero x hm r φ u.val (curve u.val) (hr u.val u.property)
  · intro u i hi
    exact gradient_zero x hm r φ u.val (curve u.val) (hr u.val u.property) i hi
  · intro u HZ
    exact havoid u.val u.property ⟨(0,j), HZ⟩

theorem nonzero_of_anchor (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : IntegralMixedRelativeCuts.Choices x hm r φ)
    (a b : ℝ) (curve : ℝ → Fin (n+1) → ℝ) (hc : ContinuousOn curve (Icc a b))
    (hr : ∀ t ∈ Ioo a b, curve t ∈ physical x hm r φ t)
    (havoid : ∀ t ∈ Ioo a b, t ∉ bad x hm r φ c) (s t : Ioo a b) (j : Free r)
    (hs : curve s.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j) ≠ 0) :
    curve t.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j) ≠ 0 :=
  fun HZ => hs ((zero_iff x hm r φ c a b curve hc hr havoid s t j).mpr HZ)

end LeanCanny.Connectivity.IntegralMixedSelectedCoordinateStatus

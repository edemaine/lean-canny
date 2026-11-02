/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameCritical
public import LeanCanny.Connectivity.IntegralMixedSelectedComponentSampling
public import LeanCanny.Encoding.BoundedRegularLowModularTerm
public import LeanCanny.Geometry.BoundedRegularComponents

/-! # Actual component samples in bounded regular frozen frames

Properness is proved for the original bounded regular source. Coordinate
reordering and the current-Q affine sweep preserve every old component;
the existing singular-safe sampler then constructs an actual critical point.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Connectivity LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem slice_closed {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ) :
    IsClosed (slice P F values) := by
  have HP : Continuous (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y) := by
    simpa only [MvPolynomial.eval₂_eq_eval_map] using MvPolynomial.continuous_eval
      ((FermatCriticalHomogenization.polynomial P.low P.leading P.degree).map (Int.castRingHom ℝ))
  change IsClosed ({y | (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂
    (Int.castRingHom ℝ) y=0}∩{y | ∀ i∈F.frozen,(F.scales i:ℝ)*y i=(F.heights i).evaluate values})
  apply (isClosed_eq HP continuous_const).inter
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro _
  exact isClosed_eq ((continuous_apply i).const_mul _) continuous_const

theorem fiber_isCompact {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (t : ℝ)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y)) :
    IsCompact (slice P (coarse F h) values∩{y | projection F values h y=t}) := by
  apply (hp.isCompact_preimage (isCompact_singleton : IsCompact ({0} : Set ℝ))).of_isClosed_subset
  · apply (slice_closed P (coarse F h) values).inter
    exact isClosed_eq (((continuous_apply h).const_mul _).sub continuous_const) continuous_const
  · intro y hy
    exact hy.1.1

theorem regular_source_proper (R : BoundedFullWriter.Readers) (q : List Bool) :
    IsProperMap (fun y : Fin (R.dim q+4)→ℝ=>
      (FermatCriticalHomogenization.polynomial (BoundedRegularLowModularTerm.source R q).low
        (BoundedRegularLowModularTerm.source R q).leading (BoundedRegularLowModularTerm.source R q).degree).eval₂
        (Int.castRingHom ℝ) y) := by
  rw [BoundedRegularLowModularTerm.source_polynomial]
  exact BoundedRegularSource.proper _ _ _ _

theorem exists_component_sample (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (y : Fin (n+1)→ℝ)
    (hy : y∈slice P (coarse F h) values∩{y | projection F values h y=t})
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y)) :
    ∃ a : Fin (n+1)→ℝ,
      a∈connectedComponentIn (slice P (coarse F h) values∩{y | projection F values h y=t}) y ∧
      (a ∘ FrozenCoordinateOrdering.permutation F.frozen)∈IntegralMixedSelectedPhysicalFiber.physical
        (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen))
        hm (sweep x F h hh g hg) φ t := by
  let E:=spatialHomeomorph (FrozenCoordinateOrdering.permutation F.frozen)
  let K:=slice P (coarse F h) values∩{y | projection F values h y=t}
  let x':=IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)
  let r:=sweep x F h hh g hg
  have HE : LeanCanny.Connectivity.IntegralMixedSelectedComponentSampling.fiber x' hm r φ t=E '' K := by
    change sweepSlice x hm φ F h hh g hg t=E '' K
    rw [sweepSlice_eq x hm φ F h hh g hg values H t]
    ext z
    change (E.symm z∈K)↔z∈E '' K
    exact (Set.ext_iff.mp (E.image_eq_preimage_symm K) z).symm
  have HC : IsCompact (LeanCanny.Connectivity.IntegralMixedSelectedComponentSampling.fiber x' hm r φ t) :=
    HE ▸ (fiber_isCompact P F values h t hp).image E.continuous
  have HY : E y∈LeanCanny.Connectivity.IntegralMixedSelectedComponentSampling.fiber x' hm r φ t := by
    rw [HE]
    exact mem_image_of_mem E hy
  obtain ⟨a,ha,hphys⟩:=LeanCanny.Connectivity.IntegralMixedSelectedComponentSampling.exists_component_critical
    x' hm r φ t HC (E y) HY
  have Hcomp:=E.image_connectedComponentIn hy
  rw [←HE] at Hcomp
  rw [←Hcomp] at ha
  obtain ⟨a,ha,rfl⟩:=ha
  exact ⟨a,ha,hphys⟩

/-- The concrete original-source instance has no compactness or critical-point premise. -/
theorem regular_component_sample (R : BoundedFullWriter.Readers) (q : List Bool)
    (x : State (BoundedRegularLowModularTerm.source R q) S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame (R.dim q+3))
    (h : Fin (R.dim q+4)) (hh : h∈F.frozen) (g : Fin (R.dim q+4)) (hg : g∉F.frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (y : Fin (R.dim q+4)→ℝ)
    (hy : y∈slice (BoundedRegularLowModularTerm.source R q) (coarse F h) values∩
      {y | projection F values h y=t}) :
    ∃ a : Fin (R.dim q+4)→ℝ,
      a∈connectedComponentIn (slice (BoundedRegularLowModularTerm.source R q) (coarse F h) values∩
        {y | projection F values h y=t}) y ∧
      (a ∘ FrozenCoordinateOrdering.permutation F.frozen)∈IntegralMixedSelectedPhysicalFiber.physical
        (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen))
        hm (sweep x F h hh g hg) φ t :=
  exists_component_sample x hm φ F h hh g hg values H t y hy (regular_source_proper R q)

end LeanCanny.Geometry.IntegralMixedFrozenFrame

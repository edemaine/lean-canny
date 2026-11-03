/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealCriticalValues
/-! # Fiber paths and projection charts away from actual real critical values

The existing chart and component arguments require actual regularity only.
No nonvanishing of a polynomial with extraneous height roots is assumed.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
theorem locallyPathConnected_of_realCriticalValues (x : State P S B m ι) (_hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (_hh : h∈F.frozen)
    (values : Fin m→ℝ) (_H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (ht : t∉realCriticalValues P F values h) :
    LocallyPathConnectedSpace (shiftedSlice P F values h t) := by
  have HE:=shiftedSlice_eq_fiber P F values h t
  let : LocallyPathConnectedSpace (RegularFiber.Fiber (constraintMap P F) (constraintTarget F values h t)) :=
    RegularFiber.locallyPathConnected (constraintMap P F) (constraintTarget F values h t)
      (fun _=>(constraintMap_contDiff P F).contDiffAt.of_le (by simp))
      (fun y=>by
        rw [constraintMap_derivative]
        exact regular_of_not_realCriticalValue P F values h t ht y.val (HE ▸ y.property))
  exact (Homeomorph.setCongr HE).symm.locallyPathConnectedSpace

theorem joinedIn_of_realCriticalValues (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (ht : t∉realCriticalValues P F values h)
    (y : Fin (n+1)→ℝ) (hy : y∈shiftedSlice P F values h t) (z : Fin (n+1)→ℝ)
    (hz : z∈connectedComponentIn (shiftedSlice P F values h t) y) :
    JoinedIn (shiftedSlice P F values h t) y z := by
  let : LocallyPathConnectedSpace (shiftedSlice P F values h t):=
    locallyPathConnected_of_realCriticalValues x hm φ F h hh values H t ht
  exact RegularFiberComponentPaths.joinedIn_of_component _ y hy z hz

theorem exists_charts_of_realCriticalValues (x : State P S B m ι) (_hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (values : Fin m→ℝ) (_H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (A B : ℝ) (hheight : ∀ t∈Ioo A B,t∉realCriticalValues P F values h) :
    ∃ chart : ∀ y : (coarseProjection P F values h) ⁻¹' Ioo A B,
      OpenPartialHomeomorph ((coarseProjection P F values h) ⁻¹' Ioo A B)
        (Ioo A B × (fderiv ℝ (constraintMap P F) y.val.val).ker),
      (∀ y,y∈(chart y).source) ∧
      ∀ z y,y∈(chart z).source→(chart z y).1=(Ioo A B).restrictPreimage (coarseProjection P F values h) y := by
  let r : Option F.frozen:=some ⟨h,hh⟩
  have HD (y : Fin (n+1)→ℝ)
      (hy : constraintMap P F y∈CoordinateLineInterval.region (constraintTarget F values h 0) r A B) :
      Function.Surjective (fderiv ℝ (constraintMap P F) y) := by
    have HY : y∈slice P (coarse F h) values := (constraint_coarse_eq P F values h hh) ▸ hy.1
    let z : ConstraintLineCharts.coarseSet (constraintMap P F) (constraintTarget F values h 0) r:=⟨y,hy.1⟩
    have HT : projection F values h y∈Ioo A B := by
      rw [←constraint_projection P F values h hh z]
      exact hy.2
    have HF : y∈shiftedSlice P F values h (projection F values h y) :=
      (Set.ext_iff.mp (shiftedSlice_fiber P F values h hh _) y).mpr ⟨HY,rfl⟩
    rw [constraintMap_derivative]
    exact regular_of_not_realCriticalValue P F values h _ (hheight _ HT) y HF
  obtain ⟨C,HC,HF⟩:=ConstraintLineCharts.exists_charts (constraintMap P F) (constraintTarget F values h 0) r A B
    (fun _ _=>(constraintMap_contDiff P F).contDiffAt.of_le le_top) HD
  let e:=chartDomainHomeomorph P F values h hh A B
  let chart (y : (coarseProjection P F values h) ⁻¹' Ioo A B):=
    e.toOpenPartialHomeomorph.trans (C (e y))
  refine ⟨chart,fun y=>⟨mem_univ y,HC (e y)⟩,?_⟩
  intro z y hy
  have HE:=HF (e z) (e y) hy.2
  apply Subtype.ext
  exact (congrArg Subtype.val HE).trans (constraint_projection P F values h hh (e y).val)

theorem exists_path_sample_of_realCriticalValues (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (ht : t∉realCriticalValues P F values h)
    (y : Fin (n+1)→ℝ) (hy : y∈shiftedSlice P F values h t)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y)) :
    ∃ a : Fin (n+1)→ℝ, JoinedIn (shiftedSlice P F values h t) y a ∧
      (a ∘ FrozenCoordinateOrdering.permutation F.frozen)∈IntegralMixedSelectedPhysicalFiber.physical
        (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen))
        hm (sweep x F h hh g hg) φ t := by
  have HY:=((Set.ext_iff.mp (shiftedSlice_fiber P F values h hh t) y).mp hy)
  obtain ⟨a,ha,hphys⟩:=exists_component_sample x hm φ F h hh g hg values H t y HY hp
  rw [←shiftedSlice_fiber P F values h hh t] at ha
  exact ⟨a,joinedIn_of_realCriticalValues x hm φ F h hh values H t ht y hy a ha,hphys⟩

end LeanCanny.Geometry.IntegralMixedFrozenFrame

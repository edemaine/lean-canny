/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameProjection

/-! # Actual coarse projection charts away from current height cuts -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem exists_charts (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (A B : ℝ) (hheight : ∀ t∈Ioo A B,(heightCut x hm F h).eval₂ φ.toRingHom t≠0) :
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
    exact regular_of_heightCut x hm φ F h hh values H _ (hheight _ HT) y HF
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

end LeanCanny.Geometry.IntegralMixedFrozenFrame

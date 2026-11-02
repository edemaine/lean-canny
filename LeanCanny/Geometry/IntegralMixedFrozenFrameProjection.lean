/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSections
public import LeanCanny.Geometry.ConstraintLineCharts

/-! # Proper projection and literal constraint-line coordinates of the coarse frame -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open scoped Classical
variable {n : ℕ}

noncomputable def coarseProjection {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ) (h : Fin (n+1)) :
    slice P (coarse F h) values→ℝ := fun y=>projection F values h y.val

theorem coarse_compact {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ) (h : Fin (n+1))
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y)) :
    IsCompact (slice P (coarse F h) values) := by
  apply (hp.isCompact_preimage (isCompact_singleton : IsCompact ({0} : Set ℝ))).of_isClosed_subset
    (slice_closed P (coarse F h) values)
  intro y hy
  exact hy.1

theorem coarseProjection_continuous {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ) (h : Fin (n+1)) :
    Continuous (coarseProjection P F values h) :=
  (((continuous_apply h).comp continuous_subtype_val).const_mul _).sub continuous_const

theorem coarseProjection_proper {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ) (h : Fin (n+1))
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y)) :
    IsProperMap (coarseProjection P F values h) := by
  let : CompactSpace (slice P (coarse F h) values):=isCompact_iff_compactSpace.mp (coarse_compact P F values h hp)
  exact (coarseProjection_continuous P F values h).isProperMap

theorem constraint_coarse_eq {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (hh : h∈F.frozen) :
    ConstraintLineCharts.coarseSet (constraintMap P F) (constraintTarget F values h 0) (some ⟨h,hh⟩)=
      slice P (coarse F h) values := by
  ext y
  constructor
  · intro hy
    refine ⟨hy none (by simp),?_⟩
    intro i hi
    have HI:=Finset.mem_erase.mp hi
    have HN : (some (⟨i,HI.2⟩ : F.frozen))≠some ⟨h,hh⟩:=fun He=>HI.1 (congrArg Subtype.val (Option.some.inj He))
    have HE:=(constraintMap_some P F y ⟨i,HI.2⟩).symm.trans (hy _ HN)
    simpa only [constraintTarget,coarse,ite_eq_right HI.1,add_zero] using HE
  · intro hy j hj
    cases j with
    | none=>exact hy.1
    | some j=>
      have HN : j.val≠h:=fun He=>hj (congrArg some (Subtype.ext He))
      have HE:=hy.2 j.val (Finset.mem_erase.mpr ⟨HN,j.property⟩)
      simpa only [constraintTarget,coarse,ite_eq_right HN,add_zero] using (constraintMap_some P F y j).trans HE

theorem constraint_projection {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (hh : h∈F.frozen)
    (y : ConstraintLineCharts.coarseSet (constraintMap P F) (constraintTarget F values h 0) (some ⟨h,hh⟩)) :
    ConstraintLineCharts.projection (constraintMap P F) (constraintTarget F values h 0) (some ⟨h,hh⟩) y=
      projection F values h y.val := by
  change constraintMap P F y.val (some ⟨h,hh⟩)-constraintTarget F values h 0 (some ⟨h,hh⟩)=_
  rw [constraintMap_some]
  simp only [constraintTarget,ite_true,add_zero]
  rfl

noncomputable def chartDomainHomeomorph {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (hh : h∈F.frozen) (A B : ℝ) :
    (coarseProjection P F values h) ⁻¹' Ioo A B ≃ₜ
      (ConstraintLineCharts.projection (constraintMap P F) (constraintTarget F values h 0) (some ⟨h,hh⟩)) ⁻¹' Ioo A B where
  toFun y:=by
    let z : ConstraintLineCharts.coarseSet (constraintMap P F) (constraintTarget F values h 0) (some ⟨h,hh⟩):=
      ⟨y.val.val,(Set.ext_iff.mp (constraint_coarse_eq P F values h hh) y.val.val).mpr y.val.property⟩
    have HE : ConstraintLineCharts.projection (constraintMap P F) (constraintTarget F values h 0) (some ⟨h,hh⟩) z=
        coarseProjection P F values h y.val:=constraint_projection P F values h hh z
    have HZ : ConstraintLineCharts.projection (constraintMap P F) (constraintTarget F values h 0) (some ⟨h,hh⟩) z∈Ioo A B := by
      rw [HE]
      exact y.property
    exact ⟨z,HZ⟩
  invFun y:=by
    let z : slice P (coarse F h) values:=
      ⟨y.val.val,(Set.ext_iff.mp (constraint_coarse_eq P F values h hh) y.val.val).mp y.val.property⟩
    have HE : ConstraintLineCharts.projection (constraintMap P F) (constraintTarget F values h 0) (some ⟨h,hh⟩) y.val=
        coarseProjection P F values h z:=constraint_projection P F values h hh y.val
    have HZ : coarseProjection P F values h z∈Ioo A B := by
      rw [←HE]
      exact y.property
    exact ⟨z,HZ⟩
  left_inv _:=rfl
  right_inv _:=rfl
  continuous_toFun:=((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun:=((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

end LeanCanny.Geometry.IntegralMixedFrozenFrame

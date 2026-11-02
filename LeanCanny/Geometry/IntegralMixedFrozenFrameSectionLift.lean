/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameCharts

/-! # Literal coarse-slice sections and their fiber paths -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open scoped Classical
variable {n : ℕ}

theorem image_fiber {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (hh : h∈F.frozen) (t : ℝ) :
    Subtype.val '' ((coarseProjection P F values h) ⁻¹' {t})=shiftedSlice P F values h t := by
  rw [shiftedSlice_fiber P F values h hh t]
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z.property,hz⟩
  · intro hy
    exact ⟨⟨y,hy.1⟩,hy.2,rfl⟩

theorem joined_fiber_iff {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (hh : h∈F.frozen) (t : ℝ)
    (y z : slice P (coarse F h) values) (hy : coarseProjection P F values h y=t) (hz : coarseProjection P F values h z=t) :
    JoinedIn ((coarseProjection P F values h) ⁻¹' {t}) y z↔JoinedIn (shiftedSlice P F values h t) y.val z.val := by
  have HE:=Topology.IsEmbedding.subtypeVal.isInducing.joinedIn_image
    (F:=(coarseProjection P F values h) ⁻¹' {t}) (x:=y) (y:=z) hy hz
  rw [image_fiber P F values h hh t] at HE
  exact HE.symm

theorem exists_lift {k : ℕ} {J : Type} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (hh : h∈F.frozen) (A B : ℝ) (t₀ : Ioo A B)
    (curve : J→ℝ→Fin (n+1)→ℝ) (HC : ∀ j,ContinuousOn (curve j) (Icc A B))
    (HR : ∀ j t,t∈Icc A B→curve j t∈shiftedSlice P F values h t)
    (HS : ∀ t : Ioo A B,∀ y∈shiftedSlice P F values h t.val,∃ j,
      JoinedIn (shiftedSlice P F values h t.val) y (curve j t.val)) :
    ∃ arc : J→ℝ→slice P (coarse F h) values,
      (∀ j,ContinuousOn (arc j) (Icc A B)) ∧
      (∀ j t,t∈Icc A B→coarseProjection P F values h (arc j t)=t) ∧
      (∀ j t,t∈Icc A B→(arc j t).val=curve j t) ∧
      ∀ t : Ioo A B,∀ y : slice P (coarse F h) values,
        coarseProjection P F values h y=t.val→∃ j,
          JoinedIn ((coarseProjection P F values h) ⁻¹' {t.val}) y (arc j t.val) := by
  have Hroot (j : J) (t : ℝ) (ht : t∈Icc A B) :
      curve j t∈slice P (coarse F h) values∩{y | projection F values h y=t}:=
    (Set.ext_iff.mp (shiftedSlice_fiber P F values h hh t) _).mp (HR j t ht)
  let anchor (j : J) : slice P (coarse F h) values:=⟨curve j t₀.val,(Hroot j _ (Ioo_subset_Icc_self t₀.property)).1⟩
  let arc (j : J) (t : ℝ) : slice P (coarse F h) values:=
    if ht : t∈Icc A B then ⟨curve j t,(Hroot j t ht).1⟩ else anchor j
  have HA (j : J) : ContinuousOn (arc j) (Icc A B) := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (HC j).congr
    intro t ht
    simp only [arc,dite_eq_left ht,Function.comp_apply]
  have HL (j : J) (t : ℝ) (ht : t∈Icc A B) : coarseProjection P F values h (arc j t)=t := by
    simp only [arc,dite_eq_left ht]
    exact (Hroot j t ht).2
  have HV (j : J) (t : ℝ) (ht : t∈Icc A B) : (arc j t).val=curve j t := by simp only [arc,dite_eq_left ht]
  refine ⟨arc,HA,HL,HV,?_⟩
  intro t y hy
  have HY : y.val∈shiftedSlice P F values h t.val:=
    (Set.ext_iff.mp (shiftedSlice_fiber P F values h hh t.val) y.val).mpr ⟨y.property,hy⟩
  obtain ⟨j,HJ⟩:=HS t y.val HY
  refine ⟨j,(joined_fiber_iff P F values h hh t.val y (arc j t.val) hy
    (HL j t.val (Ioo_subset_Icc_self t.property))).mpr ?_⟩
  rw [HV j t.val (Ioo_subset_Icc_self t.property)]
  exact HJ

end LeanCanny.Geometry.IntegralMixedFrozenFrame

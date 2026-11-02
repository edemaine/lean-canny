/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameCutContinue
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSlabCover

/-! # Exact endpoint-fiber transport for actual descending frames -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open scoped Classical
variable {n : ℕ}

noncomputable def fiberHomeomorph {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (hh : h∈F.frozen) (a : ℝ) :
    (coarseProjection P F values h) ⁻¹' {a} ≃ₜ shiftedSlice P F values h a where
  toFun y:=⟨y.val.val,(Set.ext_iff.mp (shiftedSlice_fiber P F values h hh a) y.val.val).mpr ⟨y.val.property,y.property⟩⟩
  invFun y:=by
    have HY:=(Set.ext_iff.mp (shiftedSlice_fiber P F values h hh a) y.val).mp y.property
    exact ⟨⟨y.val,HY.1⟩,HY.2⟩
  left_inv _:=rfl
  right_inv _:=rfl
  continuous_toFun:=(continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun:=(continuous_subtype_val.subtype_mk _).subtype_mk _

noncomputable def endpointHomeomorph {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F) (a : ℝ) :
    (coarseProjection P (line F h) values h) ⁻¹' {a} ≃ₜ
      slice P (advance F h) (Fin.cons a values) :=
  (fiberHomeomorph P (line F h) values h (Finset.mem_insert_self h F.frozen) a).trans
    (Homeomorph.setCongr ((line_slice P F h hh HF values a).trans (slice_advance P F h hh values a).symm))

noncomputable def coarseLineHomeomorph {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (hh : h∉F.frozen) : slice P F values ≃ₜ slice P (coarse (line F h) h) values :=
  Homeomorph.setCongr (congrArg (fun G=>slice P G values) (coarse_line F h hh)).symm

theorem endpoint_point {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F) (a : ℝ)
    (y : (coarseProjection P (line F h) values h) ⁻¹' {a}) :
    (endpointHomeomorph P F values h hh HF a y).val=y.val.val := rfl

end LeanCanny.Geometry.IntegralMixedFrozenFrame

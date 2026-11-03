/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalFrameRetained
/-! # A retained endpoint extends the chronological frozen descriptor

Freezing the next physical coordinate appends its already retained producer
label. It consumes no scalar birth and lowers the free rank by one.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalFrame.Descriptor
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ}

def freeze (d : Descriptor n birth) (label : Fin birth) (hk : d.labels.length<n+1) : Descriptor n birth where
  labels:=d.labels++[label]
  length_le:=by simp only [List.length_append,List.length_singleton];omega

theorem freeze_length (d : Descriptor n birth) (label : Fin birth) (hk : d.labels.length<n+1) :
    (d.freeze label hk).labels.length=d.labels.length+1:=by
  simp only [freeze,List.length_append,List.length_singleton]

theorem freeze_reference_old (d : Descriptor n birth) (label : Fin birth) (hk : d.labels.length<n+1)
    (i : Fin d.labels.length) :
    (d.freeze label hk).reference ⟨i.val,by rw [d.freeze_length];omega⟩=d.reference i :=by
  apply Fin.ext
  change birth-1-((d.labels++[label]).get ⟨i.val,by
    simp only [List.length_append,List.length_singleton];have :=i.isLt;omega⟩).val=
      birth-1-(d.labels.get i).val
  simp only [List.get_eq_getElem,List.getElem_append_left i.isLt]

theorem freeze_reference_last (d : Descriptor n birth) (label : Fin birth) (hk : d.labels.length<n+1) :
    (d.freeze label hk).reference ⟨d.labels.length,by rw [d.freeze_length];omega⟩=
      (⟨birth-1-label.val,by have :=label.isLt;omega⟩ : Fin birth) :=by
  apply Fin.ext
  change birth-1-((d.labels++[label]).get ⟨d.labels.length,by
    simp only [List.length_append,List.length_singleton];omega⟩).val=birth-1-label.val
  simp only [List.get_eq_getElem,List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero]

theorem freeze_rank (d : Descriptor n birth) (label : Fin birth) (hk : d.labels.length<n+1) :
    n+1-(d.freeze label hk).frame.frozen.card+1=n+1-d.frame.frozen.card :=by
  rw [(d.freeze label hk).frozen_card,d.frozen_card,d.freeze_length]
  omega

theorem freeze_slice (d : Descriptor n birth) (label : Fin birth) (hk : d.labels.length<n+1)
    (P : SpatialSource n) (values : Fin birth→ℝ) :
    slice P (d.freeze label hk).frame values=
      slice P d.frame values∩{point | point ⟨d.labels.length,hk⟩=
        values ⟨birth-1-label.val,by have :=label.isLt;omega⟩} :=by
  ext point
  rw [(d.freeze label hk).slice_iff]
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨H,Hlevels⟩
    refine ⟨(d.slice_iff P values point).mpr ⟨H,?_⟩,?_⟩
    · intro i
      have HI:=Hlevels ⟨i.val,by rw [d.freeze_length];omega⟩
      rw [d.freeze_reference_old label hk i] at HI
      exact HI
    · have HI:=Hlevels ⟨d.labels.length,by rw [d.freeze_length];omega⟩
      rw [d.freeze_reference_last label hk] at HI
      exact HI
  · rintro ⟨H,Hlast⟩
    obtain ⟨HP,Hlevels⟩:=(d.slice_iff P values point).mp H
    refine ⟨HP,?_⟩
    intro i
    by_cases hi : i.val<d.labels.length
    · have HE : (d.freeze label hk).reference i=d.reference ⟨i.val,hi⟩:=
        d.freeze_reference_old label hk ⟨i.val,hi⟩
      rw [HE]
      exact Hlevels ⟨i.val,hi⟩
    · have Hi : i.val<d.labels.length+1:=by simpa only [d.freeze_length] using i.isLt
      have HE : i=(⟨d.labels.length,by rw [d.freeze_length];exact Nat.lt_succ_self _⟩ :
          Fin (d.freeze label hk).labels.length):=
        Fin.ext (by change i.val=d.labels.length;omega)
      rw [HE,d.freeze_reference_last label hk]
      exact Hlast

end LeanCanny.Geometry.IntegralMixedChronologicalFrame.Descriptor

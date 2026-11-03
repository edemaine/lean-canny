/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalFrame
public import LeanCanny.Geometry.IntegralMixedPointCompanionReadback
/-! # Every coordinate has a chronological producer after ordered capture

Frozen coordinates use their existing producer labels. The remaining
coordinates use the literal critical companion births, in the same newest
first order as the companion interpreter. Equality of these scalar fields
therefore identifies the entire physical point across independent histories.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalFrame.Descriptor
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedPointCompanion
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ}

def freeCount (d : Descriptor n birth) :=n+1-d.labels.length

noncomputable def freeCoordinate (d : Descriptor n birth) (i : Fin d.freeCount) : Free d.frame.frozen :=
  ⟨⟨d.labels.length+i.val,by have :=i.isLt;have :=d.length_le;unfold freeCount at *;omega⟩,
    by rw [d.frozen_mem];change ¬d.labels.length+i.val<d.labels.length;omega⟩

noncomputable def orderedFree (d : Descriptor n birth) :=List.ofFn d.freeCoordinate

theorem orderedFree_length (d : Descriptor n birth) : d.orderedFree.length=d.freeCount:=List.length_ofFn

theorem orderedFree_get (d : Descriptor n birth) (i : Fin d.orderedFree.length) :
    ((d.orderedFree.get i).val).val=d.labels.length+i.val :=by
  simp only [orderedFree,List.get_eq_getElem,List.getElem_ofFn,freeCoordinate]

def pointProducer (d : Descriptor n birth) (i : Fin (n+1)) : Fin (birth+d.freeCount) :=
  if hi : i.val<d.labels.length then
    ⟨(d.labels.get ⟨i.val,hi⟩).val,by have :=(d.labels.get ⟨i.val,hi⟩).isLt;omega⟩
  else ⟨birth+d.freeCount-1-(i.val-d.labels.length),by
    have :=i.isLt
    have :=d.length_le
    unfold freeCount at *
    omega⟩

def pointReference (d : Descriptor n birth) (i : Fin (n+1)) : Fin (birth+d.freeCount) :=
  ⟨birth+d.freeCount-1-(d.pointProducer i).val,by have :=(d.pointProducer i).isLt;omega⟩

theorem pointReference_frozen (d : Descriptor n birth) (i : Fin (n+1)) (hi : i.val<d.labels.length) :
    (d.pointReference i).val=d.freeCount+(d.reference ⟨i.val,hi⟩).val :=by
  change birth+d.freeCount-1-(d.pointProducer i).val=_
  rw [pointProducer,dite_eq_left hi]
  have :=(d.labels.get ⟨i.val,hi⟩).isLt
  change birth+d.freeCount-1-(d.labels.get ⟨i.val,hi⟩).val=
    d.freeCount+(birth-1-(d.labels.get ⟨i.val,hi⟩).val)
  omega

theorem pointReference_free (d : Descriptor n birth) (i : Fin (n+1)) (hi : ¬i.val<d.labels.length) :
    (d.pointReference i).val=i.val-d.labels.length :=by
  change birth+d.freeCount-1-(d.pointProducer i).val=_
  rw [pointProducer,dite_eq_right hi]
  change birth+d.freeCount-1-(birth+d.freeCount-1-(i.val-d.labels.length))=i.val-d.labels.length
  have :=i.isLt
  unfold freeCount
  omega

theorem point_values (d : Descriptor n birth) (P : SpatialSource n) (old : Fin birth→ℝ)
    (p : Fin (n+1)→ℝ) (hp : p∈slice P d.frame old) (i : Fin (n+1)) :
    values p old d.orderedFree ⟨(d.pointReference i).val,by rw [d.orderedFree_length];exact (d.pointReference i).isLt⟩=p i :=by
  by_cases hi : i.val<d.labels.length
  · have HE : (⟨(d.pointReference i).val,by rw [d.orderedFree_length];exact (d.pointReference i).isLt⟩ :
        Fin (birth+d.orderedFree.length))=
        ⟨d.orderedFree.length+(d.reference ⟨i.val,hi⟩).val,by have :=(d.reference ⟨i.val,hi⟩).isLt;omega⟩:=by
      apply Fin.ext
      change (d.pointReference i).val=d.orderedFree.length+(d.reference ⟨i.val,hi⟩).val
      rw [d.orderedFree_length,d.pointReference_frozen i hi]
    rw [HE,values_old]
    exact ((d.slice_iff P old p).mp hp).2 ⟨i.val,hi⟩ |>.symm
  · have HI : i.val-d.labels.length<d.orderedFree.length:=by
      rw [d.orderedFree_length]
      have :=i.isLt
      unfold freeCount
      omega
    let j : Fin d.orderedFree.length:=⟨i.val-d.labels.length,HI⟩
    have HE : (⟨(d.pointReference i).val,by rw [d.orderedFree_length];exact (d.pointReference i).isLt⟩ :
        Fin (birth+d.orderedFree.length))=⟨j.val,by have :=j.isLt;omega⟩:=
      Fin.ext (d.pointReference_free i hi)
    rw [HE,values_get]
    apply congrArg p
    apply Fin.ext
    rw [d.orderedFree_get]
    change d.labels.length+(i.val-d.labels.length)=i.val
    omega

theorem point_eq_iff (d : Descriptor n birth) {m : ℕ} (e : Descriptor n m)
    (P : SpatialSource n) (old : Fin birth→ℝ) (other : Fin m→ℝ)
    (p q : Fin (n+1)→ℝ) (hp : p∈slice P d.frame old) (hq : q∈slice P e.frame other) :
    p=q ↔ ∀i : Fin (n+1),
      values p old d.orderedFree ⟨(d.pointReference i).val,by rw [d.orderedFree_length];exact (d.pointReference i).isLt⟩=
      values q other e.orderedFree ⟨(e.pointReference i).val,by rw [e.orderedFree_length];exact (e.pointReference i).isLt⟩ :=by
  simp only [d.point_values P old p hp,e.point_values P other q hq]
  exact funext_iff

end LeanCanny.Geometry.IntegralMixedChronologicalFrame.Descriptor

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalMidpoint
public import LeanCanny.Geometry.IntegralMixedPointCompanionReadback
/-! # A midpoint signature stores its mean as two producers, never an alias -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalMidpointSignature
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedPointCompanion
open scoped Classical
set_option backward.isDefEq.respectTransparency false

inductive Feature (cap : ℕ) where
  | producer (label : Fin cap)
  | mean (left right : Fin cap)
  deriving DecidableEq

noncomputable def Feature.eval {cap : ℕ} (values : Fin cap→ℝ) : Feature cap→ℝ
  | .producer a=>values (IntegralMixedChronologicalMidpoint.reference a)
  | .mean a b=>(values (IntegralMixedChronologicalMidpoint.reference a)+
      values (IntegralMixedChronologicalMidpoint.reference b))/2

def retainLabel {birth : ℕ} (a : Fin birth) (q : ℕ) : Fin (birth+q):=⟨a.val,by have :=a.isLt;omega⟩
def freeCount {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth):=
  n+1-(d.labels.length+1)

noncomputable def freeCoordinate {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth) (i : Fin (freeCount d)) :
    Free (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen :=
  ⟨⟨d.labels.length+1+i.val,by have :=i.isLt;unfold freeCount at *;omega⟩,
    (IntegralMixedChronologicalMidpoint.free_iff d hk a b _).mpr (by
      change d.labels.length+1≤d.labels.length+1+i.val;omega)⟩

noncomputable def orderedFree {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth):=List.ofFn (freeCoordinate d hk a b)

theorem orderedFree_length {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth) : (orderedFree d hk a b).length=freeCount d:=List.length_ofFn

theorem orderedFree_get {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth) (i : Fin (orderedFree d hk a b).length) :
    ((orderedFree d hk a b).get i).val.val=d.labels.length+1+i.val :=by
  simp only [orderedFree,List.get_eq_getElem,List.getElem_ofFn,freeCoordinate]

def signature {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (a b : Fin birth) (i : Fin (n+1)) : Feature (birth+freeCount d) :=
  if hi : i.val<d.labels.length then .producer (retainLabel (d.labels.get ⟨i.val,hi⟩) (freeCount d))
  else if hm : i.val=d.labels.length then .mean (retainLabel a (freeCount d)) (retainLabel b (freeCount d))
  else .producer ⟨birth+freeCount d-1-(i.val-(d.labels.length+1)),by
    have :=i.isLt
    unfold freeCount at *
    omega⟩

noncomputable def postValues {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth) (p : Fin (n+1)→ℝ) (old : Fin birth→ℝ) :
    Fin (birth+freeCount d)→ℝ:=fun i=>values p old (orderedFree d hk a b)
      ⟨i.val,by rw [orderedFree_length];exact i.isLt⟩

theorem reference_include {birth : ℕ} (a : Fin birth) (q : ℕ) :
    (IntegralMixedChronologicalMidpoint.reference (retainLabel a q)).val=
      q+(IntegralMixedChronologicalMidpoint.reference a).val :=by
  dsimp only [IntegralMixedChronologicalMidpoint.reference,retainLabel]
  have :=a.isLt
  omega

theorem postValues_old {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b c : Fin birth) (p : Fin (n+1)→ℝ) (old : Fin birth→ℝ) :
    Feature.eval (postValues d hk a b p old) (.producer (retainLabel c (freeCount d)))=
      old (IntegralMixedChronologicalMidpoint.reference c) :=by
  change values p old (orderedFree d hk a b) _=_
  have HE : (⟨(IntegralMixedChronologicalMidpoint.reference (retainLabel c (freeCount d))).val,
      by rw [orderedFree_length];exact (IntegralMixedChronologicalMidpoint.reference (retainLabel c (freeCount d))).isLt⟩ :
        Fin (birth+(orderedFree d hk a b).length))=
      ⟨(orderedFree d hk a b).length+(IntegralMixedChronologicalMidpoint.reference c).val,
        by have :=(IntegralMixedChronologicalMidpoint.reference c).isLt;omega⟩:=by
    apply Fin.ext
    change (IntegralMixedChronologicalMidpoint.reference (retainLabel c (freeCount d))).val=
      (orderedFree d hk a b).length+(IntegralMixedChronologicalMidpoint.reference c).val
    rw [reference_include,orderedFree_length]
  rw [HE,values_old]

 theorem signature_mean {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (a b : Fin birth) (i : Fin (n+1)) (hi : i.val=d.labels.length) :
    signature d a b i=.mean (retainLabel a (freeCount d)) (retainLabel b (freeCount d)) :=by
  unfold signature
  rw [dite_eq_right (by omega),dite_eq_left hi]

theorem point_values {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth) (P : SpatialSource n)
    (old : Fin birth→ℝ) (p : Fin (n+1)→ℝ)
    (hp : p∈slice P (IntegralMixedChronologicalMidpoint.frame d hk a b) old) (i : Fin (n+1)) :
    Feature.eval (postValues d hk a b p old) (signature d a b i)=p i :=by
  have HS:=hp
  rw [IntegralMixedChronologicalMidpoint.slice_eq] at HS
  by_cases hi : i.val<d.labels.length
  · rw [signature,dite_eq_left hi,postValues_old]
    have HH:=((d.slice_iff P old p).mp HS.1).2 ⟨i.val,hi⟩
    exact HH.symm
  · by_cases hm : i.val=d.labels.length
    · rw [signature_mean d a b i hm]
      change (Feature.eval (postValues d hk a b p old) (.producer (retainLabel a (freeCount d)))+
        Feature.eval (postValues d hk a b p old) (.producer (retainLabel b (freeCount d))))/2=p i
      rw [postValues_old,postValues_old]
      have HE : i=IntegralMixedChronologicalMidpoint.next d hk:=Fin.ext hm
      exact HS.2.symm.trans (congrArg p HE.symm)
    · have HI : i.val-(d.labels.length+1)<(orderedFree d hk a b).length:=by
        rw [orderedFree_length]
        have :=i.isLt
        unfold freeCount
        omega
      let j : Fin (orderedFree d hk a b).length:=⟨i.val-(d.labels.length+1),HI⟩
      rw [signature,dite_eq_right hi,dite_eq_right hm]
      let label : Fin (birth+freeCount d):=⟨birth+freeCount d-1-(i.val-(d.labels.length+1)),by
        have :=i.isLt;unfold freeCount at *;omega⟩
      change values p old (orderedFree d hk a b)
        ⟨(IntegralMixedChronologicalMidpoint.reference label).val,
          by rw [orderedFree_length];exact (IntegralMixedChronologicalMidpoint.reference label).isLt⟩=p i
      have HE : (⟨(IntegralMixedChronologicalMidpoint.reference label).val,
          by rw [orderedFree_length];exact (IntegralMixedChronologicalMidpoint.reference label).isLt⟩ :
            Fin (birth+(orderedFree d hk a b).length))=⟨j.val,by have :=j.isLt;omega⟩:=by
        apply Fin.ext
        change birth+freeCount d-1-label.val=j.val
        dsimp only [label,j]
        have :=i.isLt
        unfold freeCount at *
        omega
      rw [HE,values_get]
      apply congrArg p
      apply Fin.ext
      rw [orderedFree_get]
      dsimp only [j]
      omega

end LeanCanny.Geometry.IntegralMixedChronologicalMidpointSignature

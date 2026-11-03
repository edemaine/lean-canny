/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalFrame
/-! # Retention preserves chronological labels and the actual frozen frame -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalFrame.Descriptor
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ}

def retain (d : Descriptor n birth) : Descriptor n (birth+1) where
  labels:=d.labels.map Fin.castSucc
  length_le:=by simpa only [List.length_map] using d.length_le

theorem retain_length (d : Descriptor n birth) : d.retain.labels.length=d.labels.length:=by
  simp only [retain,List.length_map]

theorem atom_retain (d : Descriptor n birth) (i : Fin (n+1)) :
    d.retain.atom i=laterAtom (d.atom i) :=by
  unfold atom
  by_cases hi : i.val<d.labels.length
  · have HI : i.val<d.retain.labels.length:=by simpa only [d.retain_length] using hi
    rw [dite_eq_left HI,dite_eq_left hi]
    change some (d.retain.reference ⟨i.val,HI⟩)=
      some (d.reference ⟨i.val,hi⟩).succ
    apply congrArg some
    apply Fin.ext
    have HE : ((d.labels.map Fin.castSucc).get ⟨i.val,by simpa only [List.length_map] using hi⟩).val=
        (d.labels.get ⟨i.val,hi⟩).val:=by
      simp only [List.get_eq_getElem,List.getElem_map,Fin.val_castSucc]
    change birth+1-1-((d.labels.map Fin.castSucc).get ⟨i.val,HI⟩).val=
      birth-1-(d.labels.get ⟨i.val,hi⟩).val+1
    rw [HE]
    have HB:=(d.labels.get ⟨i.val,hi⟩).isLt
    omega
  · have HI : ¬i.val<d.retain.labels.length:=by simpa only [d.retain_length] using hi
    rw [dite_eq_right HI,dite_eq_right hi]
    rfl

theorem frame_retain (d : Descriptor n birth) : d.retain.frame=retained d.frame :=by
  unfold frame retained originalFrame
  simp only [d.retain_length]
  congr 1
  funext i
  rw [d.atom_retain i]
  exact laterAtom_value (d.atom i)

theorem atom_word (d : Descriptor n birth) (i : Fin (n+1)) :
    (d.atom i).word=if hi : i.val<d.labels.length then
      pair [true] (BinaryNatCode.encode ((d.labels.get ⟨i.val,hi⟩)).val) else [] :=by
  unfold atom
  split_ifs with hi
  · change referenceWord birth (birth-1-((d.labels.get ⟨i.val,hi⟩)).val)=_
    have HB:=((d.labels.get ⟨i.val,hi⟩)).isLt
    have HR : birth-1-((d.labels.get ⟨i.val,hi⟩)).val<birth:=by omega
    have HE : birth-1-(birth-1-((d.labels.get ⟨i.val,hi⟩)).val)=
        ((d.labels.get ⟨i.val,hi⟩)).val:=by omega
    simp only [referenceWord,HR,decide_true,HE]
  · rfl

theorem atom_word_retain (d : Descriptor n birth) (i : Fin (n+1)) :
    (d.retain.atom i).word=(d.atom i).word :=by
  rw [d.retain.atom_word i,d.atom_word i]
  simp only [retain,List.length_map,List.get_eq_getElem,List.getElem_map,Fin.val_castSucc]

end LeanCanny.Geometry.IntegralMixedChronologicalFrame.Descriptor

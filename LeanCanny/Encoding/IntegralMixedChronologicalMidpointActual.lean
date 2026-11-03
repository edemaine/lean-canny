/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalMidpointCode
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameCodeActual
public import LeanCanny.Geometry.IntegralMixedChronologicalMidpoint
/-! # The label-only midpoint code is the actual original point-rule record -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalMidpointCode
open LeanCanny.Algebra IntegralMixedHistory
open LeanCanny.Geometry LeanCanny.Geometry.IntegralMixedFrozenFrame
open IntegralMixedCausalRowConstructor IntegralMixedCriticalRecordConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ}
open IntegralMixedChronologicalFrameCode (labels labels_count)

noncomputable def data (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    IntegralMixedCriticalRecordConstructor.Data n birth :=
  originalPointData (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk)) (IntegralMixedChronologicalMidpoint.rows d hk a b) g j hg hj

theorem data_rule (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    (data d hk a b g j hg hj).rule=pointRule (IntegralMixedChronologicalMidpoint.frame d hk a b) g hg j hj :=
  originalPointData_rule _ _ _ _ _ _ _

theorem row_base_actual (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (i : Fin (n+1)) :
    (IntegralMixedChronologicalMidpoint.rows d hk a b i).base=IntegralMixedChronologicalFrameCode.row (labels d) i.val :=by
  by_cases hi : i=IntegralMixedChronologicalMidpoint.next d hk
  · subst i
    simp only [IntegralMixedChronologicalMidpoint.rows,ite_true,Row.base,IntegralMixedChronologicalFrameCode.row,labels_count,
      IntegralMixedChronologicalMidpoint.next,Nat.lt_irrefl,ite_false]
  · simp only [IntegralMixedChronologicalMidpoint.rows,ite_eq_right hi,Row.base]
    exact (IntegralMixedChronologicalFrameCode.row_actual d i).symm

theorem row_mid_actual (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (i : Fin (n+1)) :
    (IntegralMixedChronologicalMidpoint.rows d hk a b i).midpoint=midRow (labels d) a.val b.val i.val :=by
  by_cases hi : i=IntegralMixedChronologicalMidpoint.next d hk
  · subst i
    simp only [IntegralMixedChronologicalMidpoint.rows,ite_true,Row.midpoint,midRow,labels_count,IntegralMixedChronologicalMidpoint.next,ite_true,IntegralMixedChronologicalMidpoint.reference_word,producerWord]
  · have HN : i.val≠d.labels.length:=fun h=>hi (Fin.ext h)
    simp only [IntegralMixedChronologicalMidpoint.rows,ite_eq_right hi,Row.midpoint,midRow,labels_count,ite_eq_right HN]

theorem data_rows (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    WordList.encode (List.ofFn (fun i=>((data d hk a b g j hg hj).rows i).base))=
      IntegralMixedChronologicalFrameCode.rows n (labels d) :=by
  unfold data originalPointData
  simp only [(IntegralMixedChronologicalMidpoint.prefix_frozen d hk a b).permutation,Equiv.refl_apply]
  apply congrArg WordList.encode
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_map,List.length_range]
  · intro i hi hj
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
    exact row_base_actual d hk a b ⟨i,hi⟩

theorem data_midRows (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    WordList.encode (List.ofFn (fun i=>((data d hk a b g j hg hj).rows i).midpoint))=
      midRows n (labels d) a.val b.val :=by
  unfold data originalPointData
  simp only [(IntegralMixedChronologicalMidpoint.prefix_frozen d hk a b).permutation,Equiv.refl_apply]
  apply congrArg WordList.encode
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_map,List.length_range]
  · intro i hi hj
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
    exact row_mid_actual d hk a b ⟨i,hi⟩

theorem data_doubles (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    List.ofFn (data d hk a b g j hg hj).double=doubles n (labels d) :=by
  unfold data originalPointData doubles
  simp only [(IntegralMixedChronologicalMidpoint.prefix_frozen d hk a b).permutation,Equiv.refl_apply]
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_map,List.length_range]
  · intro i hi hj
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range,midpointDouble,Fin.ext_iff,IntegralMixedChronologicalMidpoint.next,labels_count]

theorem data_code (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    (data d hk a b g j hg hj).code=code n (labels d) a.val b.val g.val j.val :=by
  unfold IntegralMixedCriticalRecordConstructor.Data.code code
  rw [data_rows d hk a b g j hg hj,data_midRows d hk a b g j hg hj,data_doubles d hk a b g j hg hj,labels_count]
  have HO : (data d hk a b g j hg hj).offset.val=d.labels.length+1:=IntegralMixedChronologicalMidpoint.frozen_card d hk a b
  have HG : (data d hk a b g j hg hj).objective.val=g.val-(d.labels.length+1):=by
    change ((FrozenCoordinateOrdering.permutation (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen).symm g).val-
      (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen.card=g.val-(d.labels.length+1)
    rw [(IntegralMixedChronologicalMidpoint.prefix_frozen d hk a b).permutation,IntegralMixedChronologicalMidpoint.frozen_card]
    rfl
  have HJ : (data d hk a b g j hg hj).coordinate.val=j.val-(d.labels.length+1):=by
    change ((FrozenCoordinateOrdering.permutation (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen).symm j).val-
      (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen.card=j.val-(d.labels.length+1)
    rw [(IntegralMixedChronologicalMidpoint.prefix_frozen d hk a b).permutation,IntegralMixedChronologicalMidpoint.frozen_card]
    rfl
  rw [HG,HJ,HO]

end LeanCanny.Encoding.IntegralMixedChronologicalMidpointCode

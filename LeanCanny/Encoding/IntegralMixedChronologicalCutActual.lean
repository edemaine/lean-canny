/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalCutCode
public import LeanCanny.Geometry.IntegralMixedChronologicalSweepFrame
/-! # The chronological cut compiler emits the actual current-Q cut record -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalCutCode
open LeanCanny.Algebra LeanCanny.Geometry IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedChronologicalSweepFrame IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedCutRecordConstructor.word IntegralMixedCausalRecordDegree.withDegree
variable {n birth : ℕ}

theorem data_rows (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen) :
    WordList.encode (List.ofFn (fun i=>((pointData d hk g j hg hj).rows i).base))=
      IntegralMixedChronologicalFrameCode.rows n (IntegralMixedChronologicalFrameCode.labels d) :=by
  unfold pointData originalPointData
  simp only [(prefix_frozen d hk).permutation,Equiv.refl_apply,IntegralMixedCausalRowConstructor.Row.base]
  apply congrArg WordList.encode
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_map,List.length_range]
  · intro i hi hj
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
    exact (IntegralMixedChronologicalFrameCode.row_actual d ⟨i,hi⟩).symm

theorem data_code (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen)
    (tag : Tag) (choice degree : ℕ) :
    (data d hk g j hg hj).code tag choice degree=
      code n (IntegralMixedChronologicalFrameCode.labels d) g.val j.val
        (IntegralMixedCutRecordConstructor.tagIndex tag) choice degree :=by
  have HO : (pointData d hk g j hg hj).offset.val=d.labels.length+1:=pointData_offset d hk g j hg hj
  have HG : (pointData d hk g j hg hj).objective.val=g.val-(d.labels.length+1):=by
    change ((FrozenCoordinateOrdering.permutation (frame d hk).frozen).symm g).val-
      (frame d hk).frozen.card=g.val-(d.labels.length+1)
    rw [(prefix_frozen d hk).permutation,frozen_card]
    rfl
  have HJ : (pointData d hk g j hg hj).coordinate.val=j.val-(d.labels.length+1):=by
    change ((FrozenCoordinateOrdering.permutation (frame d hk).frozen).symm j).val-
      (frame d hk).frozen.card=j.val-(d.labels.length+1)
    rw [(prefix_frozen d hk).permutation,frozen_card]
    rfl
  unfold IntegralMixedCutRecordConstructor.Data.code code
  apply congrArg (fun w=>IntegralMixedCausalRecordDegree.withDegree w degree)
  unfold IntegralMixedCutRecordConstructor.Data.baseCode
  change IntegralMixedCutRecordConstructor.word (pointData d hk g j hg hj).offset.val
    (pointData d hk g j hg hj).objective.val (pointData d hk g j hg hj).coordinate.val d.labels.length
    (IntegralMixedCutRecordConstructor.tagIndex tag) choice
    (WordList.encode (List.ofFn (fun i=>((pointData d hk g j hg hj).rows i).base)))
    (WordList.encode (List.ofFn (fun i=>((pointData d hk g j hg hj).rows i).midpoint)))
    (List.ofFn (pointData d hk g j hg hj).double) true=_
  rw [data_rows,IntegralMixedChronologicalFrameCode.labels_count,HG,HJ,HO]
  simp only [pointData,originalPointData,IntegralMixedCausalRowConstructor.Row.midpoint,List.ofFn_const,emptyRows]

theorem cut_decode {n B birth : ℕ} (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen)
    (P : SpatialSource n) (tag : Tag) (choice degree : ℕ)
    (hd : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) :
    IntegralMixedCausalUnitRecordBits.cut P (data d hk g j hg hj).ambient_positive birth
      (code n (IntegralMixedChronologicalFrameCode.labels d) g.val j.val
        (IntegralMixedCutRecordConstructor.tagIndex tag) choice degree) hcap=
      (data d hk g j hg hj).cut P tag choice degree hd hcap :=by
  rw [←data_code d hk g j hg hj tag choice degree]
  exact IntegralMixedCutRecordConstructor.cut_decode _ P tag choice degree hd hcap

theorem code_size {n B birth : ℕ} (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen)
    (tag : Tag) (choice degree : ℕ) (hc : choice≤2^B) (hd : degree≤2^B) :
    (code n (IntegralMixedChronologicalFrameCode.labels d) g.val j.val
      (IntegralMixedCutRecordConstructor.tagIndex tag) choice degree).length≤
      IntegralMixedCutRecordConstructor.codeBudget n birth B :=by
  rw [←data_code d hk g j hg hj tag choice degree]
  exact IntegralMixedCutRecordConstructor.Data.code_length _ tag choice degree hc hd

theorem command_decode {n B birth : ℕ} (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen)
    (P : SpatialSource n) (hn : 0<n) (tag : Tag) (choice degree : ℕ)
    (hd : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (Q : ℤ) (hQ : Q≠0) :
    (IntegralMixedCausalUnitRecordBits.record P hn birth
      (code n (IntegralMixedChronologicalFrameCode.labels d) g.val j.val
        (IntegralMixedCutRecordConstructor.tagIndex tag) choice degree) hcap).template.command Q hQ=
      .cut ((data d hk g j hg hj).rule Q hQ)
        (((data d hk g j hg hj).cut P tag choice degree hd hcap).kind Q hQ)
        degree hd (hd.trans hcap) :=by
  rw [←data_code d hk g j hg hj tag choice degree]
  simp only [IntegralMixedCausalUnitRecordBits.record,IntegralMixedUnitRecordCode.critical,
    IntegralMixedCutRecordConstructor.field_0,show ([] : List Bool)[0]?.getD false=false from rfl,
    Bool.false_eq_true,ite_false,Template.command]
  rw [IntegralMixedCutRecordConstructor.cut_decode]
  rfl

end LeanCanny.Encoding.IntegralMixedChronologicalCutCode

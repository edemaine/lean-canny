/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalMeanCutCode
public import LeanCanny.Geometry.IntegralMixedChronologicalMeanCut
/-! # The native mean-centered word decodes to the actual current-Q cut -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalMeanCutCode
open LeanCanny.Algebra LeanCanny.Geometry IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalMeanCut IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedCutRecordConstructor.word IntegralMixedCausalRecordDegree.withDegree
variable {n birth : ℕ}

theorem data_code (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (tag : Tag) (choice degree : ℕ) :
    (data d hk a b g j hg hj).code tag choice degree=
      code n (IntegralMixedChronologicalFrameCode.labels d) a.val b.val g.val j.val
        (IntegralMixedCutRecordConstructor.tagIndex tag) choice degree:=by
  have HO:=data_offset d hk a b g j hg hj
  have HG : (data d hk a b g j hg hj).critical.objective.val=g.val-(d.labels.length+1):=by
    change ((FrozenCoordinateOrdering.permutation (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen).symm g).val-
      (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen.card=g.val-(d.labels.length+1)
    rw [(IntegralMixedChronologicalMidpoint.prefix_frozen d hk a b).permutation,
      IntegralMixedChronologicalMidpoint.frozen_card]
    rfl
  have HJ : (data d hk a b g j hg hj).critical.coordinate.val=j.val-(d.labels.length+1):=by
    change ((FrozenCoordinateOrdering.permutation (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen).symm j).val-
      (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen.card=j.val-(d.labels.length+1)
    rw [(IntegralMixedChronologicalMidpoint.prefix_frozen d hk a b).permutation,
      IntegralMixedChronologicalMidpoint.frozen_card]
    rfl
  unfold IntegralMixedCutRecordConstructor.Data.code code
  apply congrArg (fun w=>IntegralMixedCausalRecordDegree.withDegree w degree)
  unfold IntegralMixedCutRecordConstructor.Data.baseCode
  change IntegralMixedCutRecordConstructor.word (data d hk a b g j hg hj).critical.offset.val
    (data d hk a b g j hg hj).critical.objective.val (data d hk a b g j hg hj).critical.coordinate.val
    d.labels.length (IntegralMixedCutRecordConstructor.tagIndex tag) choice
    (WordList.encode (List.ofFn (fun i=>((IntegralMixedChronologicalMidpointCode.data d hk a b g j hg hj).rows i).base)))
    (WordList.encode (List.ofFn (fun i=>((IntegralMixedChronologicalMidpointCode.data d hk a b g j hg hj).rows i).midpoint)))
    (List.ofFn (IntegralMixedChronologicalMidpointCode.data d hk a b g j hg hj).double) true=_
  rw [IntegralMixedChronologicalMidpointCode.data_rows,IntegralMixedChronologicalMidpointCode.data_midRows,
    IntegralMixedChronologicalMidpointCode.data_doubles,IntegralMixedChronologicalFrameCode.labels_count,HG,HJ,HO]

theorem command_decode {B : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (P : SpatialSource n) (hn : 0<n) (tag : Tag) (choice degree : ℕ)
    (hd : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (Q : ℤ) (hQ : Q≠0) :
    (IntegralMixedCausalUnitRecordBits.record P hn birth
      (code n (IntegralMixedChronologicalFrameCode.labels d) a.val b.val g.val j.val
        (IntegralMixedCutRecordConstructor.tagIndex tag) choice degree) hcap).template.command Q hQ=
      .cut ((data d hk a b g j hg hj).rule Q hQ)
        (((data d hk a b g j hg hj).cut P tag choice degree hd hcap).kind Q hQ)
        degree hd (hd.trans hcap):=by
  rw [←data_code d hk a b g j hg hj tag choice degree]
  simp only [IntegralMixedCausalUnitRecordBits.record,IntegralMixedUnitRecordCode.critical,
    IntegralMixedCutRecordConstructor.field_0,show ([] : List Bool)[0]?.getD false=false from rfl,
    Bool.false_eq_true,ite_false,Template.command]
  rw [IntegralMixedCutRecordConstructor.cut_decode]
  rfl

theorem code_size {B : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (tag : Tag) (choice degree : ℕ) (hc : choice≤2^B) (hd : degree≤2^B) :
    (code n (IntegralMixedChronologicalFrameCode.labels d) a.val b.val g.val j.val
      (IntegralMixedCutRecordConstructor.tagIndex tag) choice degree).length≤
      IntegralMixedCutRecordConstructor.codeBudget n birth B:=by
  rw [←data_code d hk a b g j hg hj tag choice degree]
  exact IntegralMixedCutRecordConstructor.Data.code_length _ tag choice degree hc hd

end LeanCanny.Encoding.IntegralMixedChronologicalMeanCutCode

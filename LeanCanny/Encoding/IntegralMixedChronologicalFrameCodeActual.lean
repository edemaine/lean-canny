/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameCode
/-! # The native chronological writer is an actual original point record -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalFrameCode
open LeanCanny.Algebra IntegralMixedHistory
open LeanCanny.Geometry LeanCanny.Geometry.IntegralMixedFrozenFrame
open IntegralMixedCausalRowConstructor IntegralMixedCriticalRecordConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ}

def labels (d : IntegralMixedChronologicalFrame.Descriptor n birth) : List Bool :=
  WordList.encode (d.labels.map (fun i=>BinaryNatCode.encode i.val))

theorem labels_count (d : IntegralMixedChronologicalFrame.Descriptor n birth) :
    WordListRecords.count (labels d)=d.labels.length :=by
  simp only [labels,WordListRecords.count_encode,List.length_map]

theorem labels_lookup (d : IntegralMixedChronologicalFrame.Descriptor n birth) (i : ℕ)
    (hi : i<d.labels.length) :
    Nat.fromBitsLE (WordList.get (labels d) i)=(d.labels.get ⟨i,hi⟩).val :=by
  simp only [labels,WordList.get_encode,List.getElem?_map,List.getElem?_eq_getElem hi,
    Option.map_some,Option.getD_some,BinaryNatCode.encode,Nat.fromBitsLE_bits,List.get_eq_getElem]

theorem labels_good (d : IntegralMixedChronologicalFrame.Descriptor n birth) :
    Good n birth (labels d) :=by
  refine ⟨by rw [labels_count];exact d.length_le,?_⟩
  intro i hi
  rw [labels_count] at hi
  rw [labels_lookup d i hi]
  exact (d.labels.get ⟨i,hi⟩).isLt

theorem row_actual (d : IntegralMixedChronologicalFrame.Descriptor n birth) (i : Fin (n+1)) :
    row (labels d) i.val=(d.atom i).word :=by
  rw [d.atom_word i]
  unfold row
  rw [labels_count]
  split_ifs with hi
  · rw [labels_lookup d i.val hi]
  · rfl

noncomputable def data (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (g j : Fin (n+1)) (hg : g∉d.frame.frozen) (hj : j∉d.frame.frozen) :
    IntegralMixedCriticalRecordConstructor.Data n birth :=
  originalPointData d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i)) g j hg hj

theorem data_rule (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (g j : Fin (n+1)) (hg : g∉d.frame.frozen) (hj : j∉d.frame.frozen) :
    (data d g j hg hj).rule=pointRule d.frame g hg j hj :=
  originalPointData_rule d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i)) g j hg hj

theorem data_rows (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (g j : Fin (n+1)) (hg : g∉d.frame.frozen) (hj : j∉d.frame.frozen) :
    WordList.encode (List.ofFn (fun i=>((data d g j hg hj).rows i).base))=rows n (labels d) :=by
  unfold data originalPointData
  simp only [d.prefix_frozen.permutation,Equiv.refl_apply,Row.base]
  apply congrArg WordList.encode
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_map,List.length_range]
  · intro i hi hj
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
    exact (row_actual d ⟨i,hi⟩).symm

theorem data_code (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (g j : Fin (n+1)) (hg : g∉d.frame.frozen) (hj : j∉d.frame.frozen) :
    (data d g j hg hj).code=code n (labels d) g.val j.val :=by
  unfold IntegralMixedCriticalRecordConstructor.Data.code code
  rw [data_rows d g j hg hj,labels_count]
  have HO : (data d g j hg hj).offset.val=d.labels.length:=d.frozen_card
  have HG : (data d g j hg hj).objective.val=g.val-d.labels.length:=by
    change ((FrozenCoordinateOrdering.permutation d.frame.frozen).symm g).val-d.frame.frozen.card=
      g.val-d.labels.length
    rw [d.prefix_frozen.permutation,d.frozen_card]
    rfl
  have HJ : (data d g j hg hj).coordinate.val=j.val-d.labels.length:=by
    change ((FrozenCoordinateOrdering.permutation d.frame.frozen).symm j).val-d.frame.frozen.card=
      j.val-d.labels.length
    rw [d.prefix_frozen.permutation,d.frozen_card]
    rfl
  rw [HG,HJ,HO]
  congr 1
  · apply congrArg WordList.encode
    simp only [data,originalPointData,Row.midpoint,List.ofFn_const]
  · simp only [data,originalPointData,List.ofFn_const]

theorem decode (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (g j : Fin (n+1)) (hg : g∉d.frame.frozen) (hj : j∉d.frame.frozen) :
    IntegralMixedCausalUnitRecordBits.physical n birth (code n (labels d) g.val j.val)=
      pointRule d.frame g hg j hj :=by
  rw [←data_code d g j hg hj]
  exact (rule_decode _).trans (data_rule d g j hg hj)

end LeanCanny.Encoding.IntegralMixedChronologicalFrameCode

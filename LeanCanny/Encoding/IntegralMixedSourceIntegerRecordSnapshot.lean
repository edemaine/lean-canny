/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordCells
public import LeanCanny.Algebra.IntegralMixedCausalPlanOriginalRules
/-! # Actual affine rows and mixed scale masks after a charged integer prelude -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem row_nil (physical : Bool) (birth i : ℕ) :
    IntegralMixedCausalUnitRecordBits.row [] physical birth i=.constant 0 := by
  have HG (j : ℕ) : WordList.get [] j=[] := by
    simp only [WordList.get,List.length_nil,Nat.min_zero,Function.iterate_zero_apply]
    rfl
  have HF : pairFst ([] : List Bool)=[] := rfl
  have HS : pairSnd ([] : List Bool)=[] := rfl
  simp only [IntegralMixedCausalUnitRecordBits.row,IntegralMixedUnitRecordCode.field,HG,
    IntegralMixedCausalRowCode.expression,IntegralMixedCausalRowCode.midpoint,
    IntegralMixedCausalRowCode.atom,IntegralMixedCausalRowCode.active,HF,HS,
    List.getElem?_nil,Option.getD_none,Bool.false_eq_true,ite_false,false_and]


variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ)
  (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (S root 0).degree≤2^P.width root)
  (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
  (hW : ∀root,(P.degree root).size≤P.sourceWidth root)

private theorem original_get {α : Type} (root : List Bool) (b : ℕ)
    (f : Record (P.ambient root) (P.width root)→α) (d : α)
    (hi : ∀i,f (IntegralMixedSourceIntegerPrelude.record P (fun root=>S root 0) hq T N hz hT root i)=d) :
    ((originalRecords P S hn hd hcap N hq T hz hT root).reverse[b]?.map f).getD d=
      if N root≤b ∧ b<N root+IntegralMixedCausalRecordPlanBits.count root then f (step P S hn hd hcap N root (b-N root)) else d := by
  rw [←List.getElem?_map,observations P S hn hd hcap N hq T hz hT root f d hi,List.getElem?_map]
  by_cases hb : b<N root+IntegralMixedCausalRecordPlanBits.count root
  · rw [List.getElem?_range hb,Option.map_some,Option.getD_some]
    by_cases he : b<N root
    · rw [ite_eq_left he,ite_eq_right (by omega)]
    · rw [ite_eq_right he,ite_eq_left (by omega)]
  · have HR : (List.range (N root+IntegralMixedCausalRecordPlanBits.count root))[b]?=none :=
      List.getElem?_eq_none (by rw [List.length_range]; omega)
    rw [HR]
    simp only [Option.map_none,Option.getD_none,ite_eq_right (by omega : ¬(N root≤b ∧ b<N root+IntegralMixedCausalRecordPlanBits.count root))]

include hq in
private theorem physical_original (key : List Bool) :
    IntegralMixedFramedPhysicalBits.rule P (plan P S hn hd hcap N T hz hT hroom) key=
      if N (pairFst key)≤prefixLength P key ∧ prefixLength P key<N (pairFst key)+IntegralMixedCausalRecordPlanBits.count (pairFst key) then
        IntegralMixedCausalPlanBits.originalPhysical (step P S hn hd hcap N (pairFst key) (prefixLength P key-N (pairFst key)))
      else IntegralMixedFullPhysicalBits.defaultRule _ := by
  have H:=IntegralMixedCausalPlanBits.physical_rule_original P (base P S hd hcap N T hz hT hroom)
    (originalRecords P S hn hd hcap N hq T hz hT) (records_room P S hn hd hcap N hq T hz hT hroom) key
  exact H.trans (original_get P S hn hd hcap N hq T hz hT _ _ _ _ (fun _=>rfl))

private theorem virtual_original (key : List Bool) :
    ((IntegralMixedFramedHistoryFamilyBits.family P (plan P S hn hd hcap N T hz hT hroom)
      (data P S hn hd hcap N hq T hz hT hroom hW)).rule key).critical=
      if N (pairFst key)≤prefixLength P key ∧ prefixLength P key<N (pairFst key)+IntegralMixedCausalRecordPlanBits.count (pairFst key) then
        IntegralMixedCausalPlanBits.originalVirtual (step P S hn hd hcap N (pairFst key) (prefixLength P key-N (pairFst key)))
          (IntegralMixedCausalPlanBits.fallbackRule _ (hn _)).critical
      else (IntegralMixedCausalPlanBits.fallbackRule _ (hn _)).critical := by
  have H:=IntegralMixedCausalPlanBits.virtual_rule_original P (base P S hd hcap N T hz hT hroom)
    (originalRecords P S hn hd hcap N hq T hz hT) (records_room P S hn hd hcap N hq T hz hT hroom)
    hn (originalRecords_degree P S hn hd hcap N hq T hz hT) hW key
  exact H.trans (original_get P S hn hd hcap N hq T hz hT _ _ _ _ (fun _=>rfl))

include hq in
theorem physical_row (key : List Bool) (i : Fin (P.ambient (pairFst key)+1)) :
    (IntegralMixedFramedPhysicalBits.rule P (plan P S hn hd hcap N T hz hT hroom) key).heights i=rowValue P N true key i.val := by
  rw [physical_original P S hn hd hcap N hq T hz hT hroom]
  by_cases hb : N (pairFst key)≤prefixLength P key ∧ prefixLength P key<N (pairFst key)+IntegralMixedCausalRecordPlanBits.count (pairFst key)
  · rw [ite_eq_left hb]
    unfold rowValue selectedCode
    rw [ite_eq_left hb]
    unfold step IntegralMixedCausalPlanBits.originalPhysical IntegralMixedCausalUnitRecordBits.record
    simp only [show N (pairFst key)+(prefixLength P key-N (pairFst key))=prefixLength P key from by omega]
    cases IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code (pairFst key) (prefixLength P key-N (pairFst key)))
    · simp only [Bool.false_eq_true,ite_false]
      rfl
    · simp only [ite_true]
      rfl
  · rw [ite_eq_right hb]
    unfold rowValue selectedCode
    rw [ite_eq_right hb]
    rfl

theorem virtual_row (key : List Bool) (i : Fin (P.ambient (pairFst key)+1)) :
    (((IntegralMixedFramedHistoryFamilyBits.family P (plan P S hn hd hcap N T hz hT hroom)
      (data P S hn hd hcap N hq T hz hT hroom hW)).rule key).critical).heights i=rowValue P N false key i.val := by
  rw [virtual_original P S hn hd hcap N hq T hz hT hroom hW]
  by_cases hb : N (pairFst key)≤prefixLength P key ∧ prefixLength P key<N (pairFst key)+IntegralMixedCausalRecordPlanBits.count (pairFst key)
  · rw [ite_eq_left hb]
    unfold rowValue selectedCode
    rw [ite_eq_left hb]
    unfold step IntegralMixedCausalPlanBits.originalVirtual IntegralMixedCausalUnitRecordBits.record
    simp only [show N (pairFst key)+(prefixLength P key-N (pairFst key))=prefixLength P key from by omega]
    cases IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code (pairFst key) (prefixLength P key-N (pairFst key)))
    · simp only [Bool.false_eq_true,ite_false,ite_true]
      rfl
    · simp only [Bool.true_eq_false,ite_false,ite_true]
      rfl
  · rw [ite_eq_right hb]
    unfold rowValue selectedCode
    rw [ite_eq_right hb]
    change .constant 0=IntegralMixedCausalUnitRecordBits.row [] false _ _
    exact (row_nil _ _ _).symm

include hq in
theorem physical_mask (key : List Bool) (i : Fin (P.ambient (pairFst key)+1)) :
    (IntegralMixedFramedPhysicalBits.rule P (plan P S hn hd hcap N T hz hT hroom) key).scales i=
      if (mask P N true key)[i.val]?.getD false then 2 else 1 := by
  rw [physical_original P S hn hd hcap N hq T hz hT hroom]
  by_cases hb : N (pairFst key)≤prefixLength P key ∧ prefixLength P key<N (pairFst key)+IntegralMixedCausalRecordPlanBits.count (pairFst key)
  · rw [ite_eq_left hb]
    unfold mask selectedCode
    rw [ite_eq_left hb]
    unfold step IntegralMixedCausalPlanBits.originalPhysical IntegralMixedCausalUnitRecordBits.record
    simp only [show N (pairFst key)+(prefixLength P key-N (pairFst key))=prefixLength P key from by omega]
    cases IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code (pairFst key) (prefixLength P key-N (pairFst key)))
    · simp only [Bool.false_eq_true,ite_false]
      rfl
    · simp only [ite_true]
      rfl
  · rw [ite_eq_right hb]
    unfold mask selectedCode
    rw [ite_eq_right hb]
    rfl

theorem virtual_mask (key : List Bool) (i : Fin (P.ambient (pairFst key)+1)) :
    (((IntegralMixedFramedHistoryFamilyBits.family P (plan P S hn hd hcap N T hz hT hroom)
      (data P S hn hd hcap N hq T hz hT hroom hW)).rule key).critical).scales i=
      if (mask P N false key)[i.val]?.getD false then 2 else 1 := by
  rw [virtual_original P S hn hd hcap N hq T hz hT hroom hW]
  by_cases hb : N (pairFst key)≤prefixLength P key ∧ prefixLength P key<N (pairFst key)+IntegralMixedCausalRecordPlanBits.count (pairFst key)
  · rw [ite_eq_left hb]
    unfold mask selectedCode
    rw [ite_eq_left hb]
    unfold step IntegralMixedCausalPlanBits.originalVirtual IntegralMixedCausalUnitRecordBits.record
    simp only [show N (pairFst key)+(prefixLength P key-N (pairFst key))=prefixLength P key from by omega]
    cases IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code (pairFst key) (prefixLength P key-N (pairFst key)))
    · simp only [Bool.false_eq_true,ite_false,ite_true]
      rfl
    · simp only [Bool.true_eq_false,ite_false,ite_true]
      rfl
  · rw [ite_eq_right hb]
    unfold mask selectedCode
    rw [ite_eq_right hb]
    rfl

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend

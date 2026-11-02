/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCausalRecordCells
/-! # Literal original rows and scale masks agree with the actual causal plan -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCausalRecordPlanBits
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open IntegralMixedCausalRecordBits
open IntegralMixedCausalUnitRecordBits (physical virtual)
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
  (hn : ∀ root,0<P.ambient root) (hd : ∀ root b,(S root b).degree=P.degree root)
  (hcap : ∀ root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (hroom : ∀ root,count root+2≤P.cap root+1)
  (hW : ∀ root,(P.degree root).size≤P.sourceWidth root)

private theorem original_get {α : Type} (root : List Bool) (b : ℕ)
    (f : Record (P.ambient root) (P.width root)→α) (d : α) :
    ((originalRecords P S hn hd hcap root).reverse[b]?.map f).getD d=
      if b<count root then f (step P S hn hd hcap root b) else d := by
  unfold originalRecords
  rw [List.reverse_reverse,List.getElem?_map]
  by_cases hb : b<count root
  · rw [ite_eq_left hb,List.getElem?_range hb]
    rfl
  · rw [ite_eq_right hb]
    have HR : (List.range (count root))[b]?=none :=
      List.getElem?_eq_none (by simpa only [List.length_range] using Nat.le_of_not_gt hb)
    rw [HR]
    rfl

private theorem physical_original (key : List Bool) :
    IntegralMixedFramedPhysicalBits.rule P (plan P S hn hd hcap hroom) key=
      if prefixLength P key<count (pairFst key) then
        IntegralMixedCausalPlanBits.originalPhysical (step P S hn hd hcap (pairFst key) (prefixLength P key))
      else IntegralMixedFullPhysicalBits.defaultRule _ := by
  have H := IntegralMixedCausalPlanBits.physical_rule_original P (base P S hd hcap hroom)
    (originalRecords P S hn hd hcap) (fun root => (originalRecords_length P S hn hd hcap root) ▸ hroom root) key
  exact H.trans (original_get P S hn hd hcap _ _ _ _)

private theorem virtual_original (key : List Bool) :
    ((IntegralMixedFramedHistoryFamilyBits.family P (plan P S hn hd hcap hroom)
      (data P S hn hd hcap hroom hW)).rule key).critical=
      if prefixLength P key<count (pairFst key) then
        IntegralMixedCausalPlanBits.originalVirtual (step P S hn hd hcap (pairFst key) (prefixLength P key))
          (IntegralMixedCausalPlanBits.fallbackRule _ (hn _)).critical
      else (IntegralMixedCausalPlanBits.fallbackRule _ (hn _)).critical := by
  have H := IntegralMixedCausalPlanBits.virtual_rule_original P (base P S hd hcap hroom)
    (originalRecords P S hn hd hcap) (fun root => (originalRecords_length P S hn hd hcap root) ▸ hroom root)
    hn (originalRecords_degree P S hn hd hcap) hW key
  exact H.trans (original_get P S hn hd hcap _ _ _ _)

theorem physical_row (key : List Bool) (i : Fin (P.ambient (pairFst key)+1)) :
    (IntegralMixedFramedPhysicalBits.rule P (plan P S hn hd hcap hroom) key).heights i=rowValue P true key i.val := by
  rw [physical_original P S hn hd hcap hroom]
  by_cases hb : prefixLength P key<count (pairFst key)
  · rw [ite_eq_left hb]
    unfold rowValue selectedCode
    rw [ite_eq_left hb]
    unfold step IntegralMixedCausalPlanBits.originalPhysical IntegralMixedCausalUnitRecordBits.record
    cases IntegralMixedUnitRecordCode.critical (code (pairFst key) (prefixLength P key))
    · simp only [Bool.false_eq_true,ite_false]
      rfl
    · simp only [ite_true]
      rfl
  · rw [ite_eq_right hb]
    unfold rowValue selectedCode
    rw [ite_eq_right hb]
    rfl

theorem virtual_row (key : List Bool) (i : Fin (P.ambient (pairFst key)+1)) :
    (((IntegralMixedFramedHistoryFamilyBits.family P (plan P S hn hd hcap hroom)
      (data P S hn hd hcap hroom hW)).rule key).critical).heights i=rowValue P false key i.val := by
  rw [virtual_original P S hn hd hcap hroom hW]
  by_cases hb : prefixLength P key<count (pairFst key)
  · rw [ite_eq_left hb]
    unfold rowValue selectedCode
    rw [ite_eq_left hb]
    unfold step IntegralMixedCausalPlanBits.originalVirtual IntegralMixedCausalUnitRecordBits.record
    cases IntegralMixedUnitRecordCode.critical (code (pairFst key) (prefixLength P key))
    · simp only [Bool.false_eq_true,ite_false,ite_true]
      rfl
    · simp only [Bool.true_eq_false,ite_false,ite_true]
      rfl
  · rw [ite_eq_right hb]
    unfold rowValue selectedCode
    rw [ite_eq_right hb]
    change .constant 0=IntegralMixedCausalUnitRecordBits.row [] false _ _
    exact (row_nil _ _ _).symm

theorem physical_mask (key : List Bool) (i : Fin (P.ambient (pairFst key)+1)) :
    (IntegralMixedFramedPhysicalBits.rule P (plan P S hn hd hcap hroom) key).scales i=
      if (mask P true key)[i.val]?.getD false then 2 else 1 := by
  rw [physical_original P S hn hd hcap hroom]
  by_cases hb : prefixLength P key<count (pairFst key)
  · rw [ite_eq_left hb]
    unfold mask selectedCode
    rw [ite_eq_left hb]
    unfold step IntegralMixedCausalPlanBits.originalPhysical IntegralMixedCausalUnitRecordBits.record
    cases IntegralMixedUnitRecordCode.critical (code (pairFst key) (prefixLength P key))
    · simp only [Bool.false_eq_true,ite_false]
      rfl
    · simp only [ite_true]
      rfl
  · rw [ite_eq_right hb]
    unfold mask selectedCode
    rw [ite_eq_right hb]
    rfl

theorem virtual_mask (key : List Bool) (i : Fin (P.ambient (pairFst key)+1)) :
    (((IntegralMixedFramedHistoryFamilyBits.family P (plan P S hn hd hcap hroom)
      (data P S hn hd hcap hroom hW)).rule key).critical).scales i=
      if (mask P false key)[i.val]?.getD false then 2 else 1 := by
  rw [virtual_original P S hn hd hcap hroom hW]
  by_cases hb : prefixLength P key<count (pairFst key)
  · rw [ite_eq_left hb]
    unfold mask selectedCode
    rw [ite_eq_left hb]
    unfold step IntegralMixedCausalPlanBits.originalVirtual IntegralMixedCausalUnitRecordBits.record
    cases IntegralMixedUnitRecordCode.critical (code (pairFst key) (prefixLength P key))
    · simp only [Bool.false_eq_true,ite_false,ite_true]
      rfl
    · simp only [Bool.true_eq_false,ite_false,ite_true]
      rfl
  · rw [ite_eq_right hb]
    unfold mask selectedCode
    rw [ite_eq_right hb]
    rfl

end LeanCanny.Encoding.IntegralMixedCausalRecordPlanBits

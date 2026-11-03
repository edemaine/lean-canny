/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAgreement
/-! # Saved source lookup through the literal prelude/continuation boundary -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedCausalRecordBits IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ)
  (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (S root 0).degree≤2^P.width root)
  (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)

noncomputable def base : Plan P :=
  IntegralMixedSourceIntegerPrelude.plan P (fun root=>S root 0) (fun root=>hd root 0) hcap T N hz hT
    (fun root=>by have H:=hroom root; omega)

include hroom in
theorem records_room (root : List Bool) :
    (originalRecords P S hn hd hcap N hq T hz hT root).length+2≤P.cap root+1 := by
  rw [originalRecords_length]
  exact hroom root

theorem plan_as_causal : plan P S hn hd hcap N T hz hT hroom=
    IntegralMixedCausalPlanBits.plan P (base P S hd hcap N T hz hT hroom)
      (originalRecords P S hn hd hcap N hq T hz hT) (records_room P S hn hd hcap N hq T hz hT hroom) := rfl

def sourceIndex (P : Parameters) (N : List Bool→ℕ) (key : List Bool) :=
  if N (pairFst key)≤prefixLength P key ∧ prefixLength P key<N (pairFst key)+IntegralMixedCausalRecordPlanBits.count (pairFst key)
    then prefixLength P key else 0

theorem sourceIndex_unary (P : Parameters) (a : Access P) (N : List Bool→ℕ) (hN : UnaryFn N) :
    UnaryFn (sourceIndex P N) :=
  UnaryFn.ite (((BinaryFn.ofUnary (hN.comp pairFst_mem_FP)).le
    (BinaryFn.ofUnary (IntegralMixedFullHistoryFamilyBits.prefix_unary P a))).and
    ((BinaryFn.ofUnary (IntegralMixedFullHistoryFamilyBits.prefix_unary P a)).lt
      (BinaryFn.ofUnary ((hN.comp pairFst_mem_FP).add (IntegralMixedCausalRecordPlanBits.count_unary.comp pairFst_mem_FP)))))
    (IntegralMixedFullHistoryFamilyBits.prefix_unary P a) (UnaryFn.const 0)

theorem selectedSource_eq (key : List Bool) :
    IntegralMixedCausalPlanBits.selectedSource P (base P S hd hcap N T hz hT hroom)
      (originalRecords P S hn hd hcap N hq T hz hT) key=S (pairFst key) (sourceIndex P N key) := by
  unfold IntegralMixedCausalPlanBits.selectedSource
  rw [←List.getElem?_map,observations P S hn hd hcap N hq T hz hT (pairFst key)
    Record.source (S (pairFst key) 0) (fun _=>rfl),List.getElem?_map]
  by_cases hb : prefixLength P key<N (pairFst key)+IntegralMixedCausalRecordPlanBits.count (pairFst key)
  · rw [List.getElem?_range hb,Option.map_some,Option.getD_some]
    by_cases hi : prefixLength P key<N (pairFst key)
    · rw [ite_eq_left hi]
      dsimp only [sourceIndex]
      rw [ite_eq_right (by omega)]
    · rw [ite_eq_right hi]
      dsimp only [step,IntegralMixedCausalUnitRecordBits.record,sourceIndex]
      rw [ite_eq_left (by omega)]
      congr 1
      omega
  · have HE : (List.range (N (pairFst key)+IntegralMixedCausalRecordPlanBits.count (pairFst key)))[prefixLength P key]?=none :=
      List.getElem?_eq_none (by rw [List.length_range]; omega)
    rw [HE]
    dsimp only [Option.map_none,Option.getD_none,sourceIndex,base]
    rw [ite_eq_right (by omega)]
    rfl

include hq in
theorem instruction_source (key : List Bool) :
    (instruction P (plan P S hn hd hcap N T hz hT hroom) key).source=S (pairFst key) (sourceIndex P N key) := by
  rw [plan_as_causal P S hn hd hcap N hq T hz hT hroom]
  rw [IntegralMixedCausalPlanBits.instruction_source]
  exact selectedSource_eq P S hn hd hcap N hq T hz hT hroom key

theorem originalRecords_degree (root : List Bool) : ∀r∈originalRecords P S hn hd hcap N hq T hz hT root,
    r.source.degree=P.degree root := by
  intro r hr
  rw [originalRecords,List.mem_append] at hr
  rcases hr with hr|hr
  · rw [later,List.mem_reverse] at hr
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp hr
    exact hd root (N root+b)
  · obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hr
    exact hd root 0

noncomputable def data (hW : ∀root,(P.degree root).size≤P.sourceWidth root) :
    IntegralMixedFramedHistoryFamilyBits.Data P (plan P S hn hd hcap N T hz hT hroom) :=
  IntegralMixedCausalPlanBits.data P (base P S hd hcap N T hz hT hroom)
    (originalRecords P S hn hd hcap N hq T hz hT) (records_room P S hn hd hcap N hq T hz hT hroom)
    hn (originalRecords_degree P S hn hd hcap N hq T hz hT) hW

theorem tables_represent (hW : ∀root,(P.degree root).size≤P.sourceWidth root) :
    IntegralMixedFramedHeaderBits.Represents P (plan P S hn hd hcap N T hz hT hroom)
      (data P S hn hd hcap N hq T hz hT hroom hW)
      (IntegralMixedCausalPlanBits.tables P (originalRecords P S hn hd hcap N hq T hz hT)) :=
  IntegralMixedCausalPlanBits.tables_represent P (base P S hd hcap N T hz hT hroom)
    (originalRecords P S hn hd hcap N hq T hz hT) (records_room P S hn hd hcap N hq T hz hT hroom)
    hn (originalRecords_degree P S hn hd hcap N hq T hz hT) hW

noncomputable def slopeAdapter (a : Access P) (hN : UnaryFn N)
    (hW : ∀root,(P.degree root).size≤P.sourceWidth root) :
    IntegralMixedFramedCurrentQHeightBits.UnitSlope P (plan P S hn hd hcap N T hz hT hroom)
      (data P S hn hd hcap N hq T hz hT hroom hW) :=
  IntegralMixedCausalPlanBits.unitSlope P (base P S hd hcap N T hz hT hroom)
    (originalRecords P S hn hd hcap N hq T hz hT) (records_room P S hn hd hcap N hq T hz hT hroom)
    hn (originalRecords_degree P S hn hd hcap N hq T hz hT) hW a
    (metadata P S hn hd hcap N hq T hz hT a hN)

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordTables
/-! # The native tables observe the literal combined causal records

Integer coefficients and current denominators are absent from every native
mode/header/body writer. Source addresses and retained-reference labels use
absolute scalar births throughout the continuation.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem range_piecewise {α : Type} (N L : ℕ) (a : α) (f : ℕ→α) :
    (List.range (N+L)).map (fun b=>if b<N then a else f (b-N))=
      List.replicate N a++(List.range L).map f := by
  rw [List.range_add,List.map_append,List.map_map]
  congr 1
  · have H : (List.range N).map (fun b=>if b<N then a else f (b-N))=(List.range N).map (fun _=>a) := by
      apply List.map_congr_left
      intro b hb
      rw [ite_eq_left (List.mem_range.mp hb)]
    rw [H,List.map_const',List.length_range]
  · apply List.map_congr_left
    intro b _hb
    simp only [Function.comp_apply]
    rw [ite_eq_right (by omega)]
    congr 1
    omega

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ)
  (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (S root 0).degree≤2^P.width root)
  (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)

noncomputable def originalRecords (root : List Bool) :=
  later P S hn hd hcap N root++IntegralMixedSourceIntegerPrelude.records P (fun root=>S root 0) hq T N hz hT root

theorem originalRecords_length (root : List Bool) :
    (originalRecords P S hn hd hcap N hq T hz hT root).length=
      IntegralMixedCausalRecordPlanBits.count root+N root := by
  rw [originalRecords,List.length_append,later_length,IntegralMixedSourceIntegerPrelude.records_length]

theorem observations (root : List Bool) {α : Type}
    (f : Record (P.ambient root) (P.width root)→α) (a : α)
    (hi : ∀i,f (IntegralMixedSourceIntegerPrelude.record P (fun root=>S root 0) hq T N hz hT root i)=a) :
    (originalRecords P S hn hd hcap N hq T hz hT root).reverse.map f=
      (List.range (N root+IntegralMixedCausalRecordPlanBits.count root)).map
        (fun b=>if b<N root then a else f (step P S hn hd hcap N root (b-N root))) := by
  have HI : ((IntegralMixedSourceIntegerPrelude.records P (fun root=>S root 0) hq T N hz hT root).reverse.map f)=
      List.replicate (N root) a := by
    calc
      _ = (IntegralMixedSourceIntegerPrelude.records P (fun root=>S root 0) hq T N hz hT root).reverse.map (fun _=>a) := by
        apply List.map_congr_left
        intro r hr
        obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_reverse.mp hr)
        exact hi i
      _ = _ := by rw [List.map_const',List.length_reverse,IntegralMixedSourceIntegerPrelude.records_length]
  rw [originalRecords,List.reverse_append,List.map_append,HI,later,List.reverse_reverse,List.map_map]
  exact (range_piecewise (N root) (IntegralMixedCausalRecordPlanBits.count root) a
    (fun b=>f (step P S hn hd hcap N root b))).symm

theorem headerWords_eq (root : List Bool) :
    IntegralMixedCausalPlanBits.headerWords P (originalRecords P S hn hd hcap N hq T hz hT) root=headerTable P N root := by
  unfold IntegralMixedCausalPlanBits.headerWords headerTable
  apply congrArg WordList.encode
  rw [observations P S hn hd hcap N hq T hz hT root (fun r=>IntegralMixedCommandHeaderBits.encode r.template.header)
    (IntegralMixedCommandHeaderBits.encode IntegralMixedCommandHeaderBits.zero) (fun _=>rfl)]
  apply List.map_congr_left
  intro b _hb
  simp only [headerEntry,pairFst_pair,pairSnd_pair,List.length_replicate,code]
  split_ifs with hb
  · rfl
  · unfold step
    rw [IntegralMixedCausalUnitHeaderBits.record_header,hd]

theorem modeWords_eq (root : List Bool) :
    IntegralMixedCausalPlanBits.modeWords P (originalRecords P S hn hd hcap N hq T hz hT) root=modeTable P N root := by
  unfold IntegralMixedCausalPlanBits.modeWords modeTable
  apply congrArg WordList.encode
  rw [observations P S hn hd hcap N hq T hz hT root
    (fun r=>pair [IntegralMixedCausalPlanBits.templateCurrent r.template]
      (BinaryNatCode.encode (IntegralMixedCausalPlanBits.templateHeight r.template)))
    (pair [false] (BinaryNatCode.encode 0)) (fun _=>rfl)]
  apply List.map_congr_left
  intro b _hb
  simp only [modeEntry,pairFst_pair,pairSnd_pair,List.length_replicate,code]
  split_ifs with hb
  · rfl
  · unfold step IntegralMixedCausalUnitRecordBits.record
    cases hh : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code root (b-N root)) <;>
      simp only [hh,Bool.false_eq_true,ite_false,ite_true,IntegralMixedCausalPlanBits.templateCurrent,
        IntegralMixedCausalPlanBits.templateHeight,IntegralMixedCausalRecordPlanBits.mode,IntegralMixedCausalUnitRecordBits.cut]
    rfl

theorem bodyWords_eq (root : List Bool) :
    WordList.encode ((originalRecords P S hn hd hcap N hq T hz hT root).reverse.map (fun r=>r.template.body))=
      bodyTable P N root := by
  unfold bodyTable
  apply congrArg WordList.encode
  rw [observations P S hn hd hcap N hq T hz hT root (fun r=>r.template.body) [] (fun _=>rfl)]
  apply List.map_congr_left
  intro b _hb
  simp only [bodyEntry,pairFst_pair,pairSnd_pair,List.length_replicate,code]
  split_ifs with hb
  · rfl
  · unfold step
    rw [IntegralMixedCausalUnitBodyBits.record_body]
    congr 1
    omega

theorem metadata (a : Access P) (hN : UnaryFn N) :
    IntegralMixedCausalPlanBits.Metadata P (originalRecords P S hn hd hcap N hq T hz hT) :=
  IntegralMixedCausalPlanBits.metadata P a _ (mem_FP_of_eq (modeTable_FP P a hN)
    (fun root=>(modeWords_eq P S hn hd hcap N hq T hz hT root).symm))

theorem tables_native (a : Access P) (hN : UnaryFn N) :
    IntegralMixedHeaderTablesBits.Access (IntegralMixedCausalPlanBits.tables P (originalRecords P S hn hd hcap N hq T hz hT)) :=
  IntegralMixedCausalPlanBits.tables_native P a _ (mem_FP_of_eq (headerTable_FP P a hN)
    (fun root=>(headerWords_eq P S hn hd hcap N hq T hz hT root).symm))

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend

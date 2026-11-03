/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedStaticRecordPrefix
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameDecode
/-! # Actual causal instructions at an arbitrary original raw record index -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedStaticRecordLookup
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits IntegralMixedStaticRecordPrefix
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n B :ℕ} (Q :SpatialSource n) (hn :0<n)
  (hQ :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
  (N C :ℕ) (p :ℕ→Polynomial ℤ) (hp :∀i,p i≠0) (hd :∀i,(p i).natDegree≤2^B)
  (w :ℕ→List Bool)

theorem original_record_option (i :ℕ) (hi :i<C) :
    (records Q hn hQ N C p hp hd w).reverse[N+i]?=
      some (IntegralMixedCausalUnitRecordBits.record Q hn (N+i) (w i) hQ) :=by
  simp only [records,List.reverse_append,later,List.reverse_reverse]
  have HL :(originals Q hQ N p hp hd).reverse.length=N :=by rw [List.length_reverse,originals_length]
  rw [List.getElem?_append_right (by rw [HL];omega),HL,Nat.add_sub_cancel_left]
  simp only [List.getElem?_map,List.getElem?_range hi,Option.map_some]

theorem original_record (i :ℕ) (hi :i<C) :
    (records Q hn hQ N C p hp hd w).reverse[N+i]'(by
      rw [List.length_reverse,records_length];omega)=
    IntegralMixedCausalUnitRecordBits.record Q hn (N+i) (w i) hQ :=by
  have HH:=original_record_option Q hn hQ N C p hp hd w i hi
  rw [List.getElem?_eq_getElem (by rw [List.length_reverse,records_length];omega)] at HH
  exact Option.some.inj HH

theorem instruction_receipt {S :ℕ} {P :SpatialSource n}
    (x :State P S B 0 (Fin 0)) (hr :C+N≤S+1) (fallback :Instruction n B) (i :ℕ) (hi :i<C) :
    (chronological (IntegralMixedCausalPlanBits.commands x (records Q hn hQ N C p hp hd w)
      (by rw [records_length];exact hr)) (N+i)).getD fallback=
    instantiate (run x
      (paddedPast fallback (IntegralMixedCausalPlanBits.commands x (records Q hn hQ N C p hp hd w)
        (by rw [records_length];exact hr)) (N+i))
      (by rw [paddedPast_length];omega))
      (IntegralMixedCausalUnitRecordBits.record Q hn (N+i) (w i) hQ) :=by
  rw [IntegralMixedCausalPlanBits.chronological_instantiate _ _ _ fallback
    ⟨N+i,by rw [records_length];omega⟩,Option.getD_some,original_record Q hn hQ N C p hp hd w i hi]

private theorem instruction_critical {a width :ℕ} (c :Instruction a width) (P :SpatialSource a)
    (hc :PurePowerReductionBounds.dimension (a+1) P.degree≤2^width) (r :CriticalRule a)
    (he :c=⟨P,hc,.critical r⟩) :c.command=.critical r :=by cases he;rfl

theorem source_receipt {S :ℕ} {P :SpatialSource n}
    (x :State P S B 0 (Fin 0)) (hr :C+N≤S+1) (fallback :Instruction n B) (i :ℕ) (hi :i<C) :
    ((chronological (IntegralMixedCausalPlanBits.commands x (records Q hn hQ N C p hp hd w)
      (by rw [records_length];exact hr)) (N+i)).getD fallback).source=Q :=by
  rw [instruction_receipt Q hn hQ N C p hp hd w x hr fallback i hi]
  rfl

theorem critical_receipt {S :ℕ} {P :SpatialSource n}
    (x :State P S B 0 (Fin 0)) (hr :C+N≤S+1) (fallback :Instruction n B) (i :ℕ) (hi :i<C)
    (labels :List Bool) (g j :ℕ)
    (hg :IntegralMixedChronologicalFrameCode.PointGood n (N+i) labels g j)
    (hw :w i=IntegralMixedChronologicalFrameCode.code n labels g j) :
    ((chronological (IntegralMixedCausalPlanBits.commands x (records Q hn hQ N C p hp hd w)
      (by rw [records_length];exact hr)) (N+i)).getD fallback).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData n (N+i) labels g j hg).rule :=by
  have HE:=instruction_receipt Q hn hQ N C p hp hd w x hr fallback i hi
  let y:=run x (paddedPast fallback (IntegralMixedCausalPlanBits.commands x (records Q hn hQ N C p hp hd w)
    (by rw [records_length];exact hr)) (N+i)) (by rw [paddedPast_length];omega)
  have HC:=IntegralMixedChronologicalFrameCode.raw_command Q hn labels g j hg hQ
    (commonDenominator y) (commonDenominator_ne_zero y)
  have HI :instantiate y (IntegralMixedCausalUnitRecordBits.record Q hn (N+i) (w i) hQ)=
      ⟨Q,(IntegralMixedCausalUnitRecordBits.record Q hn (N+i) (w i) hQ).source_cap,
        .critical (IntegralMixedChronologicalFrameCode.rawData n (N+i) labels g j hg).rule⟩ :=by
    unfold instantiate
    apply congrArg (fun command=>Instruction.mk Q
      (IntegralMixedCausalUnitRecordBits.record Q hn (N+i) (w i) hQ).source_cap command)
    change (IntegralMixedCausalUnitRecordBits.record Q hn (N+i) (w i) hQ).template.command
      (commonDenominator y) (commonDenominator_ne_zero y)=_
    rw [hw]
    exact HC
  exact instruction_critical _ Q _ _ (HE.trans HI)
end LeanCanny.Algebra.IntegralMixedStaticRecordLookup

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameCodeActual
public import LeanCanny.Geometry.IntegralMixedPointCompanionPadding
/-! # The canonical empty-frame padding code has no birth-dependent references -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCanonicalPaddingSeed
open LeanCanny.Algebra LeanCanny.Geometry IntegralMixedHistory
open IntegralMixedFrozenFrame IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def data (n birth : ℕ) : IntegralMixedCriticalRecordConstructor.Data n birth where
 offset:=⟨0,Nat.zero_lt_succ _⟩
 objective:=⟨0,Nat.zero_lt_succ _⟩
 coordinate:=⟨0,Nat.zero_lt_succ _⟩
 double _:=false
 rows _:=.single none

noncomputable def rule (n : ℕ) :=(data n 0).rule

theorem data_rule (n birth : ℕ) : (data n birth).rule=rule n:=rfl

theorem data_code (n birth : ℕ) : (data n birth).code=IntegralMixedChronologicalFrameCode.code n [] 0 0 :=by
 have HC : WordListRecords.count ([] : List Bool)=0:=WordListRecords.count_encode []
 have HR : IntegralMixedChronologicalFrameCode.row []=fun _=>[]:=by
   funext i
   simp only [IntegralMixedChronologicalFrameCode.row,HC,Nat.not_lt_zero,ite_false]
 unfold data IntegralMixedCriticalRecordConstructor.Data.code IntegralMixedChronologicalFrameCode.code
   IntegralMixedChronologicalFrameCode.rows
 simp only [HC,Nat.sub_zero,List.ofFn_const,Row.base,Row.midpoint,Atom.word,HR,List.map_const',List.length_range]

theorem physical (n birth : ℕ) :
    IntegralMixedCausalUnitRecordBits.physical n birth (IntegralMixedChronologicalFrameCode.code n [] 0 0)=rule n:=by
 rw [←data_code n birth]
 exact (IntegralMixedCriticalRecordConstructor.rule_decode _).trans (data_rule n birth)

theorem command {n B birth : ℕ} (P : SpatialSource n) (hn : 0<n)
    (hc : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) (Q : ℤ) (hQ : Q≠0) :
    (IntegralMixedCausalUnitRecordBits.record P hn birth (IntegralMixedChronologicalFrameCode.code n [] 0 0) hc).template.command Q hQ=
      .critical (rule n) :=by
 rw [←data_code n birth]
 exact (IntegralMixedCriticalRecordConstructor.command_decode P hn _ hc Q hQ).trans
   (congrArg IntegralMixedFullHistoryScript.Command.critical (data_rule n birth))

noncomputable def instruction {n B : ℕ} (P : SpatialSource n)
    (hc : PurePowerReductionBounds.dimension (n+1) P.degree≤2^B) : IntegralMixedFramedHistoryScript.Instruction n B :=
 ⟨P,hc,.critical (rule n)⟩

theorem instantiate {n B birth S m : ℕ} {Q : SpatialSource n} {ι : Type}
    (x : State Q S B m ι) (P : SpatialSource n) (hn : 0<n)
    (hc : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) :
    IntegralMixedCausalRecordBits.instantiate x
      (IntegralMixedCausalUnitRecordBits.record P hn birth (IntegralMixedChronologicalFrameCode.code n [] 0 0) hc)=
      instruction P (IntegralMixedCausalUnitRecordBits.record P hn birth (IntegralMixedChronologicalFrameCode.code n [] 0 0) hc).source_cap :=by
 unfold IntegralMixedCausalRecordBits.instantiate instruction
 rw [command P hn hc (commonDenominator x) (commonDenominator_ne_zero x)]
 rfl

end LeanCanny.Encoding.IntegralMixedCanonicalPaddingSeed

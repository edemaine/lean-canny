/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedStaticRecordLookup
public import LeanCanny.Encoding.IntegralMixedChronologicalMidpointRaw
/-! # A literal midpoint code is the actual creating critical instruction -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedStaticRecordLookup
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits IntegralMixedStaticRecordPrefix
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n B : ℕ} (Q : SpatialSource n) (hn : 0<n)
  (hQ : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
  (N C : ℕ) (p : ℕ→Polynomial ℤ) (hp : ∀i,p i≠0) (hd : ∀i,(p i).natDegree≤2^B)
  (w : ℕ→List Bool)

private theorem critical_eq {a width : ℕ} (c : Instruction a width) (P : SpatialSource a)
    (hc : PurePowerReductionBounds.dimension (a+1) P.degree≤2^width) (r : CriticalRule a)
    (he : c=⟨P,hc,.critical r⟩) : c.command=.critical r :=by cases he;rfl

theorem midpoint_receipt {S : ℕ} {P : SpatialSource n}
    (x : State P S B 0 (Fin 0)) (hr : C+N≤S+1) (fallback : Instruction n B) (i : ℕ) (hi : i<C)
    (labels : List Bool) (a b g j : ℕ)
    (hg : IntegralMixedChronologicalMidpointCode.Good n (N+i) labels a b g j)
    (hw : w i=IntegralMixedChronologicalMidpointCode.code n labels a b g j) :
    ((chronological (IntegralMixedCausalPlanBits.commands x (records Q hn hQ N C p hp hd w)
      (by rw [records_length];exact hr)) (N+i)).getD fallback).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData n (N+i) labels a b g j hg).rule :=by
  have HE:=instruction_receipt Q hn hQ N C p hp hd w x hr fallback i hi
  let y:=run x (paddedPast fallback (IntegralMixedCausalPlanBits.commands x (records Q hn hQ N C p hp hd w)
    (by rw [records_length];exact hr)) (N+i)) (by rw [paddedPast_length];omega)
  have HC:=IntegralMixedChronologicalMidpointCode.raw_command Q hn labels a b g j hg hQ
    (commonDenominator y) (commonDenominator_ne_zero y)
  have HI : instantiate y (IntegralMixedCausalUnitRecordBits.record Q hn (N+i) (w i) hQ)=
      ⟨Q,(IntegralMixedCausalUnitRecordBits.record Q hn (N+i) (w i) hQ).source_cap,
        .critical (IntegralMixedChronologicalMidpointCode.rawData n (N+i) labels a b g j hg).rule⟩ :=by
    unfold instantiate
    apply congrArg (fun command=>Instruction.mk Q
      (IntegralMixedCausalUnitRecordBits.record Q hn (N+i) (w i) hQ).source_cap command)
    change (IntegralMixedCausalUnitRecordBits.record Q hn (N+i) (w i) hQ).template.command
      (commonDenominator y) (commonDenominator_ne_zero y)=_
    rw [hw]
    exact HC
  exact critical_eq _ Q _ _ (HE.trans HI)

end LeanCanny.Algebra.IntegralMixedStaticRecordLookup

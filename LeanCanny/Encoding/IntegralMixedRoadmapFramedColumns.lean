/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapPaddedWord
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordBank
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalScalar
/-! # The padded marked factory and actual framed physical arity

The column estimate follows the source-framed interpreter, so every record
may carry its own spatial source. Both the original prelude and final probe
are charged. The generous bound permits every birth to be critical.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRecordChain
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical

theorem Records.actual_marked_fullCount {n : List Bool→ℕ} {dimension T labels : ℕ}
    (R : Records dimension T labels) (seed probe : Word T) (candidate metadata : List Bool) :
    IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (R.root seed probe candidate metadata)=
      fullBirth dimension (n (pairFst candidate)+8) :=by
  unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
  rw [R.raw_count]
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,Records.root,pairFst_pair,
    fullBirth,maxBirth,probedRecordBound]
  omega

def framedColumnBound (n initial : ℕ) :=(2*n+4)*fullBirth n initial

theorem framedColumnBound_unary {n initial : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) :
    UnaryFn (fun q=>framedColumnBound (n q) (initial q)) :=
  (((UnaryFn.const 2).mul hn).add (UnaryFn.const 4)).mul
    ((maxBirth_unary hn hi).add (UnaryFn.const 1))

theorem actual_framed_physical_columns {n B initial : ℕ}
    (cs : List (IntegralMixedFramedHistoryScript.Instruction n B)) (hlen : cs.length≤fullBirth n initial) :
    Fintype.card (IntegralMixedFramedHistoryScript.Index (Fin 0) cs)≤framedColumnBound n initial :=by
  rw [IntegralMixedFramedPhysicalIndex.physical_card,IntegralMixedFramedPhysicalIndex.arity_eq]
  have HC : cs.countP (fun c=>c.command.isCritical)≤cs.length:=List.countP_le_length
  have HM:=Nat.mul_le_mul_left (2*n+3) HC
  have HE : cs.length+(2*n+3)*cs.length=(2*n+4)*cs.length:=by ring
  unfold framedColumnBound
  calc
    cs.length+(2*n+3)*cs.countP (fun c=>c.command.isCritical)≤cs.length+(2*n+3)*cs.length:=by omega
    _=(2*n+4)*cs.length:=HE
    _≤(2*n+4)*fullBirth n initial:=Nat.mul_le_mul_left _ hlen

end LeanCanny.Encoding.IntegralMixedRoadmapRecordChain

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRecordBudget
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordPlan
/-! # A fixed raw record count includes the final probe

The meaningful chain is padded to its dimension bound, then the final probe
is appended. Thus the existing marked factory has the declared fixed cap,
including its two spare stages. The padding word must come from an already
realized typed seed when semantic realization is needed; these byte and cap
identities alone do not assert that arbitrary copied records are realizable.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRecordChain
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical

def Records.paddedCodes {n T labels : ℕ} (R : Records n T labels) (seed probe : Word T) : List (Word T) :=
  R.codes++List.replicate (recordBound n-R.codes.length) seed++[probe]

theorem Records.paddedCodes_length {n T labels : ℕ} (R : Records n T labels) (seed probe : Word T) :
    (R.paddedCodes seed probe).length=probedRecordBound n :=by
  have HC:=R.codes_length_le
  simp only [Records.paddedCodes,List.length_append,List.length_replicate,List.length_singleton,
    probedRecordBound]
  omega

def Records.paddedWord {n T labels : ℕ} (R : Records n T labels) (seed probe : Word T) :=
  WordList.encode ((R.paddedCodes seed probe).map Subtype.val)

theorem Records.paddedWord_count {n T labels : ℕ} (R : Records n T labels) (seed probe : Word T) :
    WordListRecords.count (R.paddedWord seed probe)=probedRecordBound n :=by
  simp only [Records.paddedWord,WordListRecords.count_encode,List.length_map,R.paddedCodes_length]

theorem Records.paddedWord_length {n T labels : ℕ} (R : Records n T labels) (seed probe : Word T) :
    (R.paddedWord seed probe).length≤(2*T+2)*probedRecordBound n :=by
  have HB:=WordList.length_le ((R.paddedCodes seed probe).map Subtype.val) T (by
    intro w hw
    obtain ⟨code,_,rfl⟩:=List.mem_map.mp hw
    exact code.property)
  simpa only [Records.paddedWord,List.length_map,R.paddedCodes_length] using HB

theorem probedWordBound_unary {n initial B : List Bool→ℕ} (hn : UnaryFn n)
    (hi : BinaryFn initial) (hB : UnaryFn B) :
    UnaryFn (fun q=>(2*codeBound (n q) (initial q) (B q)+2)*probedRecordBound (n q)) :=
  (((UnaryFn.const 2).mul (codeBound_unary hn hi hB)).add (UnaryFn.const 2)).mul
    ((recordBound_unary hn).add (UnaryFn.const 1))

def Records.root {n T labels : ℕ} (R : Records n T labels) (seed probe : Word T)
    (candidate metadata : List Bool) :=pair candidate (pair (R.paddedWord seed probe) metadata)

theorem Records.raw_count {n T labels : ℕ} (R : Records n T labels) (seed probe : Word T)
    (candidate metadata : List Bool) :
    IntegralMixedCausalRecordPlanBits.count (R.root seed probe candidate metadata)=probedRecordBound n :=by
  simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
    Records.root,pairFst_pair,pairSnd_pair,R.paddedWord_count]

theorem Records.actual_marked_cap {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {dimension T labels : ℕ} (R : Records dimension T labels) (seed probe : Word T)
    (candidate metadata : List Bool) :
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap (R.root seed probe candidate metadata)=
      cap dimension (n (pairFst candidate)+8) :=by
  change IntegralMixedAuxiliaryMarkedIntegerSource.number n (R.root seed probe candidate metadata)+8+
    IntegralMixedCausalRecordPlanBits.count (R.root seed probe candidate metadata)+2=_
  rw [R.raw_count,cap_eq_probed]
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,Records.root,pairFst_pair]

end LeanCanny.Encoding.IntegralMixedRoadmapRecordChain

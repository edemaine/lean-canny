/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IndexedModulusCRT
public import LeanCanny.Algebra.PrimalitySpace
public import LeanCanny.Algebra.PrimePowerSpace
public import LeanCanny.Computation.SpaceFunctionChain

/-!
# Certified computation of an indexed CRT modulus

Input `pair N i` supplies arbitrary binary words. Trial division computes the
prime guard and bounded multiplication computes the maximal power. Sequential
composition retains the input and guard; FP selection returns the power for a
prime index and one otherwise. Native space composition certifies both stages.
-/

@[expose] public section

namespace LeanCanny.Algebra.ChineseRemainder.ModulusBits

open LeanCanny.Encoding
open LeanCanny.Computation

def select (p : List Bool) : List Bool :=
  if (pairSnd (pairFst p))[0]?.getD false then pairSnd p else [true]

theorem select_mem_FP : select ∈ FP :=
  (FPPred.getBit (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) (UnaryFn.const 0)).ite_mem_FP
    pairSnd_mem_FP (constFn_mem_FP [true])

theorem evaluator : SpaceFunction (fun c => BinaryNatCode.encode
    (indexedModulus (Nat.fromBitsLE (pairFst c)) (Nat.fromBitsLE (pairSnd c)))) := by
  let P := (PrimalityBits.evaluator.precompose pairSnd pairSnd_mem_FP).withInput
  let Q := (PrimePowerBits.evaluator.precompose pairFst pairFst_mem_FP).withInput
  let R := (P.chain Q).postcompose select select_mem_FP
  refine R.congr (funext fun c => ?_)
  simp only [Function.comp_apply, select, pairFst_pair, pairSnd_pair, List.getElem?_cons_zero, Option.getD_some]
  by_cases hp : (Nat.fromBitsLE (pairSnd c)).Prime <;> simp [hp, indexedModulus, BinaryNatCode.encode]

end LeanCanny.Algebra.ChineseRemainder.ModulusBits

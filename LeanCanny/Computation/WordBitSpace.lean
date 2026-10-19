/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BinaryBitFP
public import LeanCanny.Computation.SpaceFunctionComposition

/-!
# Bit access to a space-bounded output word

The original binary index is retained while the word evaluator runs. FP lookup
caps unary index conversion at the computed word's length, including indices
much larger than the output. The certificate accounts for retaining the query.
-/

@[expose] public section

namespace LeanCanny.Computation.WordBits
open Complexity
open LeanCanny.Encoding

def lookupQuery (p : List Bool) : List Bool := pair (pairSnd p) (pairSnd (pairFst p))
def value (f : List Bool → List Bool) (p : List Bool) : List Bool :=
  if (Nat.fromBitsLE (f (pairFst p))).testBit (Nat.fromBitsLE (pairSnd p)) then [true] else []

theorem lookupQuery_mem_FP : lookupQuery ∈ FP :=
  mem_FP_pair pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def evaluator {f : List Bool → List Bool} (E : SpaceFunction f) : SpaceFunction (value f) := by
  have hlookup := mem_FP_comp lookupQuery_mem_FP BinaryNat.bitAt_mem_FP
  let Q := ((E.precompose pairFst pairFst_mem_FP).withInput).postcompose
    (BinaryNat.bitAt ∘ lookupQuery) hlookup
  refine Q.congr (funext fun p => ?_)
  simp only [Function.comp_apply, lookupQuery, pairFst_pair, pairSnd_pair, BinaryNat.bitAt_pair, value]

theorem value_packet (f : List Bool → List Bool) (c : List Bool) (a k : ℕ)
    (hf : f c = BinaryNatCode.encode a) :
    (value f (pair c (BinaryNatCode.encode k)))[0]?.getD false = a.testBit k := by
  simp only [value, pairFst_pair, pairSnd_pair, hf, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  cases a.testBit k <;> rfl

end LeanCanny.Computation.WordBits

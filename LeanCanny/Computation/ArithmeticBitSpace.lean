/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SubtractBitSpace

/-!
# Composable arithmetic bit oracles

Uniform queries have the form `pair context binaryIndex`. Lifting source
queries through an extra selected-index field makes the product and subtraction
evaluators produce this same interface, so arithmetic bit routines compose.
-/

@[expose] public section

namespace LeanCanny.Computation.ArithmeticBits
open Complexity
open LeanCanny.Encoding

def bitValue (a : List Bool → ℕ) (p : List Bool) : List Bool :=
  if (a (pairFst p)).testBit (Nat.fromBitsLE (pairSnd p)) then [true] else []

theorem bitValue_packet (a : List Bool → ℕ) (c : List Bool) (j : ℕ) :
    (bitValue a (pair c (BinaryNatCode.encode j)))[0]?.getD false = (a c).testBit j := by
  simp only [bitValue, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  cases (a c).testBit j <;> rfl

def sourceQuery (p : List Bool) : List Bool := pair (pairFst (pairFst p)) (pairSnd p)

theorem sourceQuery_mem_FP : sourceQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

theorem sourceQuery_packet (c : List Bool) (i j : ℕ) :
    sourceQuery (pair (pair c (BinaryNatCode.encode i)) (BinaryNatCode.encode j)) = pair c (BinaryNatCode.encode j) := by
  simp only [sourceQuery, pairFst_pair, pairSnd_pair]

theorem productEvaluator {f g : List Bool → List Bool} (L : SpaceFunction f) (R : SpaceFunction g)
    (a b : List Bool → ℕ)
    (hleft : ∀ c j, (f (pair c (BinaryNatCode.encode j)))[0]?.getD false = (a c).testBit j)
    (hright : ∀ c j, (g (pair c (BinaryNatCode.encode j)))[0]?.getD false = (b c).testBit j) :
    SpaceFunction (bitValue (fun c => a c * b c)) := by
  have EL := L.precompose sourceQuery sourceQuery_mem_FP
  have ER := R.precompose sourceQuery sourceQuery_mem_FP
  exact ProductBits.evaluator EL ER pairSnd pairSnd_mem_FP (a ∘ pairFst) (b ∘ pairFst)
    (by intro p j; simp only [Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair, hleft])
    (by intro p j; simp only [Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair, hright])

theorem subtractEvaluator {f g : List Bool → List Bool} (L : SpaceFunction f) (R : SpaceFunction g)
    (a b : List Bool → ℕ)
    (hleft : ∀ c j, (f (pair c (BinaryNatCode.encode j)))[0]?.getD false = (a c).testBit j)
    (hright : ∀ c j, (g (pair c (BinaryNatCode.encode j)))[0]?.getD false = (b c).testBit j)
    (horder : ∀ c, b c ≤ a c) :
    SpaceFunction (bitValue (fun c => a c - b c)) := by
  have EL := L.precompose sourceQuery sourceQuery_mem_FP
  have ER := R.precompose sourceQuery sourceQuery_mem_FP
  exact SubtractBits.evaluator EL ER pairSnd pairSnd_mem_FP (a ∘ pairFst) (b ∘ pairFst)
    (by intro p j; simp only [Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair, hleft])
    (by intro p j; simp only [Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair, hright])
    (fun p => horder (pairFst p))

end LeanCanny.Computation.ArithmeticBits

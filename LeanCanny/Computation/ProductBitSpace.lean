/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BinaryProduct
public import LeanCanny.Computation.SumBitSpace
public import LeanCanny.Computation.SpaceFunctionChain
public import LeanCanny.Encoding.BinarySubFP

/-!
# Product bits from certified operand-bit routines

The two operands are implicit natural numbers. Their individual bits are
supplied by space-bounded routines. FP queries read a left selector and a
right shifted bit; the streamed sum-bit evaluator supplies the product carry.
No operand, shifted summand, or product is stored as a complete binary word.
-/

@[expose] public section

namespace LeanCanny.Computation.ProductBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Algebra
open scoped BigOperators

def leftIndex (p : List Bool) : List Bool := pairFst (pairSnd p)
def bitIndex (p : List Bool) : List Bool := pairSnd (pairSnd p)
def leftQuery (p : List Bool) : List Bool := pair (pairFst p) (leftIndex p)
def rightQuery (p : List Bool) : List Bool :=
  pair (pairFst p) (BinaryNat.sub (pair (bitIndex p) (leftIndex p)))

def finish (p : List Bool) : List Bool :=
  if (pairSnd (pairFst p))[0]?.getD false = true ∧
      Nat.fromBitsLE (leftIndex (pairFst (pairFst p))) ≤ Nat.fromBitsLE (bitIndex (pairFst (pairFst p))) ∧
      (pairSnd p)[0]?.getD false = true then [true] else []

def termValue (f g : List Bool → List Bool) (p : List Bool) : List Bool :=
  finish (pair (pair p (f (leftQuery p))) (g (rightQuery p)))

theorem leftIndex_mem_FP : leftIndex ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem bitIndex_mem_FP : bitIndex ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem leftQuery_mem_FP : leftQuery ∈ FP := mem_FP_pair pairFst_mem_FP leftIndex_mem_FP

theorem rightQuery_mem_FP : rightQuery ∈ FP := by
  have hs := mem_FP_comp (mem_FP_pair bitIndex_mem_FP leftIndex_mem_FP) BinaryNat.sub_mem_FP
  have he := mem_FP_pair pairFst_mem_FP hs
  refine mem_FP_of_eq (g := rightQuery) he ?_
  intro p
  simp only [Function.comp_apply, rightQuery]

theorem finish_mem_FP : finish ∈ FP := by
  have hq := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hl := FPPred.getBit (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) (UnaryFn.const 0)
  have hi := BinaryNat.le_fppred (mem_FP_comp hq leftIndex_mem_FP) (mem_FP_comp hq bitIndex_mem_FP)
  have hr := FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0)
  have he := (hl.and (hi.and hr)).ite_mem_FP (constFn_mem_FP [true]) (constFn_mem_FP [])
  refine mem_FP_of_eq (g := finish) he ?_
  intro p
  simp only [Function.comp_apply, finish]

noncomputable def termEvaluator {f g : List Bool → List Bool} (L : SpaceFunction f) (R : SpaceFunction g) :
    SpaceFunction (termValue f g) := by
  let EL := (L.precompose leftQuery leftQuery_mem_FP).withInput
  let ER := (R.precompose (rightQuery ∘ pairFst) (mem_FP_comp pairFst_mem_FP rightQuery_mem_FP)).withInput
  let E := (EL.chain ER).postcompose finish finish_mem_FP
  refine E.congr (funext fun p => ?_)
  simp only [Function.comp_apply, pairFst_pair, termValue]

theorem termValue_packet (f g : List Bool → List Bool) (a b : List Bool → ℕ)
    (hleft : ∀ c k, (f (pair c (BinaryNatCode.encode k)))[0]?.getD false = (a c).testBit k)
    (hright : ∀ c k, (g (pair c (BinaryNatCode.encode k)))[0]?.getD false = (b c).testBit k)
    (c : List Bool) (i k : ℕ) :
    termValue f g (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) =
      if (BinaryProduct.term (a c) (b c) i).testBit k then [true] else [] := by
  have hl : leftQuery (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) =
      pair c (BinaryNatCode.encode i) := by simp only [leftQuery, leftIndex, pairFst_pair, pairSnd_pair]
  have hr : rightQuery (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) =
      pair c (BinaryNatCode.encode (k - i)) := by
    simp only [rightQuery, leftIndex, bitIndex, pairFst_pair, pairSnd_pair, BinaryNat.sub_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold termValue
  rw [hl, hr]
  simp only [finish, pairFst_pair, pairSnd_pair]
  rw [hleft, hright]
  simp only [leftIndex, bitIndex, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    BinaryProduct.term_bit]
  cases (a c).testBit i <;> cases (b c).testBit (k - i) <;> by_cases hik : i ≤ k <;> simp [hik]

noncomputable def evaluator {f g : List Bool → List Bool} (L : SpaceFunction f) (R : SpaceFunction g)
    (index : List Bool → List Bool) (hi : index ∈ FP) (a b : List Bool → ℕ)
    (hleft : ∀ c k, (f (pair c (BinaryNatCode.encode k)))[0]?.getD false = (a c).testBit k)
    (hright : ∀ c k, (g (pair c (BinaryNatCode.encode k)))[0]?.getD false = (b c).testBit k) :
    SpaceFunction (fun c => if (a c * b c).testBit (Nat.fromBitsLE (index c)) then [true] else []) := by
  have hc := mem_FP_comp hi BinaryNat.succ_mem_FP
  have E := SumBits.evaluator (termEvaluator L R) (BinaryNat.succ ∘ index) index hc hi
    (fun c i => BinaryProduct.term (a c) (b c) i) (by
      intro c i k _
      rw [termValue_packet f g a b hleft hright]
      cases (BinaryProduct.term (a c) (b c) i).testBit k <;> rfl)
  refine E.congr (funext fun c => ?_)
  simp only [SumBits.value, Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits,
    BinaryProduct.product_bit]

end LeanCanny.Computation.ProductBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BinarySubtract
public import LeanCanny.Computation.ProductBitSpace

/-!
# Subtraction bits from certified operand-bit routines

For ordered implicit operands, a three-term complemented sum computes a selected
subtraction bit. Its term routines use one source bit at a time, a width guard,
and a constant carry-in. The sum-bit certificate counts every space-bounded child.
-/

@[expose] public section

namespace LeanCanny.Computation.SubtractBits

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Algebra
open scoped BigOperators

def query (p : List Bool) : List Bool := pair (pairFst p) (ProductBits.bitIndex p)

def complementFinish (index : List Bool → List Bool) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (ProductBits.bitIndex (pairFst p)) ≤ Nat.fromBitsLE (index (pairFst (pairFst p))) ∧
      ¬ (pairSnd p)[0]?.getD false = true then [true] else []

def oneValue (p : List Bool) : List Bool := if ProductBits.bitIndex p = [] then [true] else []

def termValue (f g index : List Bool → List Bool) (p : List Bool) : List Bool :=
  if ProductBits.leftIndex p = BinaryNatCode.encode 0 then f (query p)
  else if ProductBits.leftIndex p = BinaryNatCode.encode 1 then complementFinish index (pair p (g (query p)))
  else if ProductBits.leftIndex p = BinaryNatCode.encode 2 then oneValue p else []

theorem query_mem_FP : query ∈ FP := mem_FP_pair pairFst_mem_FP ProductBits.bitIndex_mem_FP

theorem oneValue_mem_FP : oneValue ∈ FP :=
  (stringEq_fppred ProductBits.bitIndex_mem_FP (constFn_mem_FP [])).ite_mem_FP (constFn_mem_FP [true]) (constFn_mem_FP [])

theorem complementFinish_mem_FP {index : List Bool → List Bool} (hi : index ∈ FP) : complementFinish index ∈ FP := by
  have hj := mem_FP_comp pairFst_mem_FP ProductBits.bitIndex_mem_FP
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hk := mem_FP_comp hc hi
  have hwidth := BinaryNat.le_fppred hj hk
  have hbit := (FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0)).not
  have he := (hwidth.and hbit).ite_mem_FP (constFn_mem_FP [true]) (constFn_mem_FP [])
  refine mem_FP_of_eq (g := complementFinish index) he ?_
  intro p
  simp only [Function.comp_apply, complementFinish]

theorem termEvaluator {f g : List Bool → List Bool} (L : SpaceFunction f) (R : SpaceFunction g)
    (index : List Bool → List Bool) (hi : index ∈ FP) : SpaceFunction (termValue f g index) := by
  have hs0 := stringEq_fppred ProductBits.leftIndex_mem_FP (constFn_mem_FP (BinaryNatCode.encode 0))
  have hs1 := stringEq_fppred ProductBits.leftIndex_mem_FP (constFn_mem_FP (BinaryNatCode.encode 1))
  have hs2 := stringEq_fppred ProductBits.leftIndex_mem_FP (constFn_mem_FP (BinaryNatCode.encode 2))
  let ER := ((R.precompose query query_mem_FP).withInput).postcompose
    (complementFinish index) (complementFinish_mem_FP hi)
  let E := SpaceFunction.branch (fun p => decide (ProductBits.leftIndex p = BinaryNatCode.encode 0)) hs0.flag_mem_FP
    (L.precompose query query_mem_FP)
    (SpaceFunction.branch (fun p => decide (ProductBits.leftIndex p = BinaryNatCode.encode 1)) hs1.flag_mem_FP ER
      (SpaceFunction.branch (fun p => decide (ProductBits.leftIndex p = BinaryNatCode.encode 2)) hs2.flag_mem_FP
        (SpaceFunction.ofFP oneValue oneValue_mem_FP) (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))))
  refine E.congr (funext fun p => ?_)
  simp only [Function.comp_apply, termValue, decide_eq_true_eq]

theorem query_packet (c : List Bool) (i j : ℕ) :
    query (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) = pair c (BinaryNatCode.encode j) := by
  simp only [query, ProductBits.bitIndex, pairFst_pair, pairSnd_pair]

theorem complementFinish_packet (index : List Bool → List Bool) (c : List Bool) (i j : ℕ) (v : List Bool)
    (b : ℕ) (hb : v[0]?.getD false = b.testBit j) :
    (complementFinish index (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) v))[0]?.getD false =
      (BinarySubtract.complement b (Nat.fromBitsLE (index c) + 1)).testBit j := by
  simp only [complementFinish, ProductBits.bitIndex, pairFst_pair, pairSnd_pair, hb,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, BinarySubtract.complement_bit]
  cases b.testBit j <;> by_cases hj : j ≤ Nat.fromBitsLE (index c) <;>
    simp [hj, show (j < Nat.fromBitsLE (index c) + 1) ↔ j ≤ Nat.fromBitsLE (index c) by omega]

theorem oneValue_packet (c : List Bool) (i j : ℕ) :
    (oneValue (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))))[0]?.getD false = (1 : ℕ).testBit j := by
  have hz : BinaryNatCode.encode j = [] ↔ j = 0 :=
    (BinaryNatCode.encode_injective.eq_iff : BinaryNatCode.encode j = BinaryNatCode.encode 0 ↔ j = 0)
  simp only [oneValue, ProductBits.bitIndex, pairSnd_pair, hz]
  by_cases hj : j = 0
  · subst j
    rfl
  · have hbit : (1 : ℕ).testBit j = false := by
      cases hb : (1 : ℕ).testBit j
      · rfl
      · exact False.elim (hj (Nat.testBit_one_eq_true_iff_self_eq_zero.mp hb))
    simp [hj, hbit]

theorem termValue_packet (f g index : List Bool → List Bool) (a b : List Bool → ℕ)
    (hleft : ∀ c j, (f (pair c (BinaryNatCode.encode j)))[0]?.getD false = (a c).testBit j)
    (hright : ∀ c j, (g (pair c (BinaryNatCode.encode j)))[0]?.getD false = (b c).testBit j)
    (c : List Bool) (i j : ℕ) (hi : i < 3) :
    (termValue f g index (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))))[0]?.getD false =
      (BinarySubtract.term (a c) (b c) (Nat.fromBitsLE (index c)) i).testBit j := by
  unfold termValue
  simp only [ProductBits.leftIndex, pairFst_pair, pairSnd_pair, BinaryNatCode.encode_injective.eq_iff]
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · simp only [↓reduceIte]
    rw [query_packet, hleft]
    rfl
  · simp only [show ¬ (1 : ℕ) = 0 by decide, ↓reduceIte]
    rw [complementFinish_packet index c 1 j _ (b c) (by rw [query_packet]; exact hright c j)]
    rfl
  · simp only [show ¬ (2 : ℕ) = 0 by decide, show ¬ (2 : ℕ) = 1 by decide, ↓reduceIte]
    rw [oneValue_packet]
    rfl

theorem evaluator {f g : List Bool → List Bool} (L : SpaceFunction f) (R : SpaceFunction g)
    (index : List Bool → List Bool) (hi : index ∈ FP) (a b : List Bool → ℕ)
    (hleft : ∀ c j, (f (pair c (BinaryNatCode.encode j)))[0]?.getD false = (a c).testBit j)
    (hright : ∀ c j, (g (pair c (BinaryNatCode.encode j)))[0]?.getD false = (b c).testBit j)
    (horder : ∀ c, b c ≤ a c) :
    SpaceFunction (fun c => if (a c - b c).testBit (Nat.fromBitsLE (index c)) then [true] else []) := by
  have E := SumBits.evaluator (termEvaluator L R index hi) (fun _ => BinaryNatCode.encode 3) index
    (constFn_mem_FP _) hi (fun c i => BinarySubtract.term (a c) (b c) (Nat.fromBitsLE (index c)) i) (by
      intro c i j hiN
      have hit : i < 3 := by simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using hiN
      exact termValue_packet f g index a b hleft hright c i j hit)
  refine E.congr (funext fun c => ?_)
  simp only [SumBits.value, BinaryNatCode.encode, Nat.fromBitsLE_bits, BinarySubtract.subtraction_bit _ _ _ (horder c)]

end LeanCanny.Computation.SubtractBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.DyadicQuotientBitFP
public import LeanCanny.Computation.SumBitSpace

/-!
# Streamed sums of dyadic quotient terms

A space-bounded preparation routine supplies a local numerator and modulus.
Retaining the bit query lets FP postprocessing read any bit of the dyadic
quotient. The sum-bit evaluator then combines all terms without storing any
complete quotient. This isolates CRT local preparation from streamed arithmetic.
-/

@[expose] public section

namespace LeanCanny.Algebra.DyadicSumBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open scoped BigOperators

def prepareQuery (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd q))

def bitQuery (precision : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (pairFst (pairSnd p)) (pair (pairSnd (pairSnd p))
    (pair (precision (pairFst (pairFst p))) (pairSnd (pairSnd (pairFst p)))))

def finish (precision : List Bool → List Bool) : List Bool → List Bool :=
  DyadicQuotientBits.value ∘ bitQuery precision

theorem prepareQuery_mem_FP : prepareQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)

theorem bitQuery_mem_FP {precision : List Bool → List Bool} (hp : precision ∈ FP) : bitQuery precision ∈ FP := by
  have ha := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hm := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hk := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
  have h := mem_FP_pair ha (mem_FP_pair hm (mem_FP_pair (mem_FP_comp hc hp) hk))
  refine mem_FP_of_eq (g := bitQuery precision) h ?_
  intro p
  simp only [Function.comp_apply, bitQuery]

theorem finish_mem_FP {precision : List Bool → List Bool} (hp : precision ∈ FP) : finish precision ∈ FP :=
  mem_FP_comp (bitQuery_mem_FP hp) DyadicQuotientBits.value_mem_FP

noncomputable def bitEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (precision : List Bool → List Bool) (hp : precision ∈ FP) :
    SpaceFunction (fun q => finish precision (pair q (f (prepareQuery q)))) :=
  ((E.precompose prepareQuery prepareQuery_mem_FP).withInput).postcompose (finish precision) (finish_mem_FP hp)

theorem bit_correct (f precision : List Bool → List Bool) (c : List Bool) (i k a m : ℕ)
    (hf : f (pair c (BinaryNatCode.encode i)) = pair (BinaryNatCode.encode a) (BinaryNatCode.encode (m - 1)))
    (hm : 0 < m) (ha : a < m) :
    finish precision (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))
      (f (prepareQuery (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))))) =
      if (2 ^ Nat.fromBitsLE (precision c) * a / m).testBit k then [true] else [] := by
  simp only [prepareQuery, pairFst_pair, pairSnd_pair, hf, finish, Function.comp_apply, bitQuery]
  rw [DyadicQuotientBits.value_pair]
  · simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (by omega : 1 ≤ m)]
  · simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (by omega : 1 ≤ m)] using ha

noncomputable def evaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count precision index : List Bool → List Bool) (hc : count ∈ FP) (hp : precision ∈ FP) (hi : index ∈ FP)
    (a m : List Bool → ℕ → ℕ)
    (hprep : ∀ c i, i < Nat.fromBitsLE (count c) →
      f (pair c (BinaryNatCode.encode i)) = pair (BinaryNatCode.encode (a c i)) (BinaryNatCode.encode (m c i - 1)))
    (hm : ∀ c i, i < Nat.fromBitsLE (count c) → 0 < m c i)
    (ha : ∀ c i, i < Nat.fromBitsLE (count c) → a c i < m c i) :
    SpaceFunction (fun c => if (∑ i ∈ Finset.range (Nat.fromBitsLE (count c)),
      2 ^ Nat.fromBitsLE (precision c) * a c i / m c i).testBit (Nat.fromBitsLE (index c))
      then [true] else []) := by
  apply SumBits.evaluator (bitEvaluator E precision hp) count index hc hi
    (fun c i => 2 ^ Nat.fromBitsLE (precision c) * a c i / m c i)
  intro c i k hiN
  rw [bit_correct f precision c i k (a c i) (m c i) (hprep c i hiN) (hm c i hiN) (ha c i hiN)]
  cases (2 ^ Nat.fromBitsLE (precision c) * a c i / m c i).testBit k <;> rfl

end LeanCanny.Algebra.DyadicSumBits

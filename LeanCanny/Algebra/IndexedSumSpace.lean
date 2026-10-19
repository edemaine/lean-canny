/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IndexedProductSpace
public import LeanCanny.Algebra.CRTPreparationSpace
public import LeanCanny.Computation.ArithmeticBitSpace

/-!
# Bits of the inverse-weighted CRT integer sum

Local preparation computes each reduced numerator. Its bits multiply the
corresponding cofactor bits through the streamed two-operand evaluator, and
the streamed sum evaluator accumulates the weighted terms. All access comes
from the supplied residue evaluator and FP modulus-bound writer.
-/

@[expose] public section

namespace LeanCanny.Algebra.ChineseRemainder.IndexedSumBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open scoped BigOperators

def numeratorValue (bound rho : List Bool → List Bool) (q : List Bool) : List Bool :=
  pairFst (PreparationBits.value bound rho q)

def cofactorQuery (z : List Bool) : List Bool :=
  pair (pairFst (pairFst z)) (pair (pairSnd (pairFst z)) (pairSnd z))

theorem cofactorQuery_mem_FP : cofactorQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)

def term (bound rho : List Bool → List Bool) (q : List Bool) : ℕ :=
  Nat.fromBitsLE (numeratorValue bound rho q) *
    IndexedProductBits.cofactor (Nat.fromBitsLE (bound (pairFst q))) (Nat.fromBitsLE (pairSnd q))

def termValue (bound rho : List Bool → List Bool) (p : List Bool) : List Bool :=
  ArithmeticBits.bitValue (term bound rho) (IndexedProductBits.factorQuery p)

noncomputable def termEvaluator {rho : List Bool → List Bool} (R : SpaceFunction rho)
    (bound : List Bool → List Bool) (hb : bound ∈ FP) : SpaceFunction (termValue bound rho) := by
  let L := WordBits.evaluator ((PreparationBits.evaluator R bound hb).postcompose pairFst pairFst_mem_FP)
  let C := (IndexedProductBits.cofactorEvaluator bound hb).precompose cofactorQuery cofactorQuery_mem_FP
  have E := ArithmeticBits.productEvaluator L C
    (fun q => Nat.fromBitsLE (numeratorValue bound rho q))
    (fun q => IndexedProductBits.cofactor (Nat.fromBitsLE (bound (pairFst q))) (Nat.fromBitsLE (pairSnd q)))
    (by
      intro q j
      simp only [WordBits.value, Function.comp_apply, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits, numeratorValue]
      cases (Nat.fromBitsLE (pairFst (PreparationBits.value bound rho q))).testBit j <;> rfl)
    (by
      intro q j
      simp only [Function.comp_apply, cofactorQuery, IndexedProductBits.cofactorValue,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      cases (IndexedProductBits.cofactor (Nat.fromBitsLE (bound (pairFst q)))
        (Nat.fromBitsLE (pairSnd q))).testBit j <;> rfl)
  exact E.precompose IndexedProductBits.factorQuery IndexedProductBits.factorQuery_mem_FP

def sourceQuery (p : List Bool) : List Bool := pair (pairFst (pairFst p)) (pairSnd p)
theorem sourceQuery_mem_FP : sourceQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

def value (bound rho : List Bool → List Bool) (p : List Bool) : List Bool :=
  if (∑ i ∈ Finset.range (Nat.fromBitsLE (bound (pairFst p)) + 1),
      term bound rho (pair (pairFst p) (BinaryNatCode.encode i))).testBit (Nat.fromBitsLE (pairSnd p))
    then [true] else []

noncomputable def evaluator {rho : List Bool → List Bool} (R : SpaceFunction rho)
    (bound : List Bool → List Bool) (hb : bound ∈ FP) : SpaceFunction (value bound rho) := by
  let E := (termEvaluator R bound hb).precompose sourceQuery sourceQuery_mem_FP
  have hcount := mem_FP_comp (mem_FP_comp pairFst_mem_FP hb) BinaryNat.succ_mem_FP
  have Q := SumBits.evaluator E (BinaryNat.succ ∘ bound ∘ pairFst) pairSnd hcount pairSnd_mem_FP
    (fun p i => term bound rho (pair (pairFst p) (BinaryNatCode.encode i))) (by
      intro p i k _
      simp only [Function.comp_apply, termValue, sourceQuery, ArithmeticBits.bitValue,
        IndexedProductBits.factorQuery, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      cases (term bound rho (pair (pairFst p) i.bits)).testBit k <;> rfl)
  refine Q.congr (funext fun p => ?_)
  simp only [SumBits.value, Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, value]

theorem term_pair (bound rho : List Bool → List Bool) (c : List Bool) (z : ℤ)
    (hres : ∀ m : ℕ, 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((z : ZMod m).val))
    (i : Fin (Nat.fromBitsLE (bound c) + 1)) :
    term bound rho (pair c (BinaryNatCode.encode i.val)) =
      (indexedSystem (Nat.fromBitsLE (bound c))).numerator
        (fun j => (z : ZMod ((indexedSystem (Nat.fromBitsLE (bound c))).modulus j)).val) i *
      (indexedSystem (Nat.fromBitsLE (bound c))).cofactor i := by
  rw [term, numeratorValue, PreparationBits.value_pair bound rho c z hres i]
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [IndexedProductBits.cofactor_eq_system _ _ i.isLt]

theorem sum_eq (bound rho : List Bool → List Bool) (c : List Bool) (z : ℤ)
    (hres : ∀ m : ℕ, 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((z : ZMod m).val)) :
    (∑ i ∈ Finset.range (Nat.fromBitsLE (bound c) + 1), term bound rho (pair c (BinaryNatCode.encode i))) =
      (indexedSystem (Nat.fromBitsLE (bound c))).integerSum
        (fun j => (z : ZMod ((indexedSystem (Nat.fromBitsLE (bound c))).modulus j)).val) := by
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  exact term_pair bound rho c z hres i

theorem value_packet (bound rho : List Bool → List Bool) (c : List Bool) (z : ℤ)
    (hres : ∀ m : ℕ, 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((z : ZMod m).val)) (k : ℕ) :
    (value bound rho (pair c (BinaryNatCode.encode k)))[0]?.getD false =
      ((indexedSystem (Nat.fromBitsLE (bound c))).integerSum
        (fun j => (z : ZMod ((indexedSystem (Nat.fromBitsLE (bound c))).modulus j)).val)).testBit k := by
  simp only [value, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hs := sum_eq bound rho c z hres
  simp only [BinaryNatCode.encode] at hs
  rw [hs]
  cases ((indexedSystem (Nat.fromBitsLE (bound c))).integerSum
    (fun j => (z : ZMod ((indexedSystem (Nat.fromBitsLE (bound c))).modulus j)).val)).testBit k <;> rfl

end LeanCanny.Algebra.ChineseRemainder.IndexedSumBits

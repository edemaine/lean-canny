/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IndexedModulusSpace
public import LeanCanny.Algebra.FiniteProductSpace
public import LeanCanny.Computation.WordBitSpace

/-!
# Uniform bits of the indexed CRT product and cofactors

The certified modulus-word evaluator supplies factor bits through bounded FP
lookup. Balanced products then compute bits of the full combined product or
any omitted-factor cofactor. Only the bound writer must be FP. There is no
assumed product-bit oracle and no stored combined product.
-/

@[expose] public section

namespace LeanCanny.Algebra.ChineseRemainder.IndexedProductBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open scoped BigOperators

def factorQuery (p : List Bool) : List Bool :=
  pair (pair (pairFst p) (pairFst (pairSnd p))) (pairSnd (pairSnd p))

def factorValue (p : List Bool) : List Bool :=
  if (indexedModulus (Nat.fromBitsLE (pairFst p)) (Nat.fromBitsLE (pairFst (pairSnd p)))).testBit
    (Nat.fromBitsLE (pairSnd (pairSnd p))) then [true] else []

theorem factorQuery_mem_FP : factorQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def factorEvaluator : SpaceFunction factorValue := by
  let E := (WordBits.evaluator ModulusBits.evaluator).precompose factorQuery factorQuery_mem_FP
  refine E.congr (funext fun p => ?_)
  simp only [Function.comp_apply, WordBits.value, factorQuery, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, factorValue]

def leafQuery (bound : List Bool → List Bool) (z : List Bool) : List Bool :=
  pair (bound (pairFst (pairFst z))) (pairSnd z)

theorem leafQuery_mem_FP {bound : List Bool → List Bool} (hb : bound ∈ FP) : leafQuery bound ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have h := mem_FP_pair (mem_FP_comp hc hb) pairSnd_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

def productValue (bound : List Bool → List Bool) (p : List Bool) : List Bool :=
  if (∏ i ∈ Finset.range (Nat.fromBitsLE (bound (pairFst p)) + 1),
      indexedModulus (Nat.fromBitsLE (bound (pairFst p))) i).testBit (Nat.fromBitsLE (pairSnd p))
      then [true] else []

def cofactor (N i : ℕ) : ℕ := ∏ j ∈ (Finset.range (N + 1)).erase i, indexedModulus N j

def cofactorValue (bound : List Bool → List Bool) (p : List Bool) : List Bool :=
  if (cofactor (Nat.fromBitsLE (bound (pairFst p))) (Nat.fromBitsLE (pairFst (pairSnd p)))).testBit
    (Nat.fromBitsLE (pairSnd (pairSnd p))) then [true] else []

theorem product_eq_range (N : ℕ) : (indexedSystem N).product =
    ∏ i ∈ Finset.range (N + 1), indexedModulus N i := by
  change (∏ i : Fin (N + 1), indexedModulus N i.val) = _
  rw [← Finset.prod_range]

theorem cofactor_eq_system (N i : ℕ) (hi : i < N + 1) :
    cofactor N i = (indexedSystem N).cofactor ⟨i, hi⟩ := by
  have hm : 0 < indexedModulus N i := (indexedSystem N).positive ⟨i, hi⟩
  have hp : cofactor N i * indexedModulus N i = (indexedSystem N).product := by
    rw [product_eq_range]
    exact Finset.prod_erase_mul _ _ (Finset.mem_range.mpr hi)
  have hs := (indexedSystem N).cofactor_mul ⟨i, hi⟩
  exact Nat.eq_of_mul_eq_mul_right hm (hp.trans hs.symm)

noncomputable def productEvaluator (bound : List Bool → List Bool) (hb : bound ∈ FP) :
    SpaceFunction (productValue bound) := by
  have hbound := mem_FP_comp pairFst_mem_FP hb
  have hcount := mem_FP_comp hbound BinaryNat.succ_mem_FP
  let E := factorEvaluator.precompose (leafQuery bound) (leafQuery_mem_FP hb)
  have Q := BalancedProduct.evaluator E (BinaryNat.succ ∘ bound ∘ pairFst) pairSnd
    hcount pairSnd_mem_FP (fun p i => indexedModulus (Nat.fromBitsLE (bound (pairFst p))) i) (by
      intro p i k _
      simp only [Function.comp_apply, leafQuery, factorValue, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]
      cases (indexedModulus (Nat.fromBitsLE (bound (pairFst p))) i).testBit k <;> rfl)
  refine Q.congr (funext fun p => ?_)
  simp only [BalancedProduct.value, Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits,
    productValue]

noncomputable def cofactorEvaluator (bound : List Bool → List Bool) (hb : bound ∈ FP) :
    SpaceFunction (cofactorValue bound) := by
  have hbound := mem_FP_comp pairFst_mem_FP hb
  have hcount := mem_FP_comp hbound BinaryNat.succ_mem_FP
  have hs := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hk := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  let E := factorEvaluator.precompose (leafQuery bound) (leafQuery_mem_FP hb)
  have Q := BalancedProduct.cofactorEvaluator E (BinaryNat.succ ∘ bound ∘ pairFst)
    (pairFst ∘ pairSnd) (pairSnd ∘ pairSnd) hcount hs hk
    (fun p i => indexedModulus (Nat.fromBitsLE (bound (pairFst p))) i) (by
      intro p i k _ _
      simp only [Function.comp_apply, leafQuery, factorValue, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]
      cases (indexedModulus (Nat.fromBitsLE (bound (pairFst p))) i).testBit k <;> rfl)
  refine Q.congr (funext fun p => ?_)
  simp only [BalancedProduct.cofactorValue, Function.comp_apply, BinaryNat.succ_eq_bits,
    Nat.fromBitsLE_bits, cofactorValue, cofactor]
  rfl

theorem productValue_packet (bound : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    (productValue bound (pair c (BinaryNatCode.encode k)))[0]?.getD false =
      (indexedSystem (Nat.fromBitsLE (bound c))).product.testBit k := by
  rw [product_eq_range]
  simp only [productValue, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  cases (∏ i ∈ Finset.range (Nat.fromBitsLE (bound c) + 1), indexedModulus (Nat.fromBitsLE (bound c)) i).testBit k <;> rfl

theorem cofactorValue_packet (bound : List Bool → List Bool) (c : List Bool) (i k : ℕ)
    (hi : i < Nat.fromBitsLE (bound c) + 1) :
    (cofactorValue bound (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false =
      ((indexedSystem (Nat.fromBitsLE (bound c))).cofactor ⟨i, hi⟩).testBit k := by
  simp only [cofactorValue, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    cofactor_eq_system _ _ hi]
  cases ((indexedSystem (Nat.fromBitsLE (bound c))).cofactor ⟨i, hi⟩).testBit k <;> rfl

end LeanCanny.Algebra.ChineseRemainder.IndexedProductBits

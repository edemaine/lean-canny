/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CofactorProductSpace

/-!
# Computing a selected modulus and its complementary product residue

The outer routine first computes the selected modulus, then feeds its positive
modulus code to the streamed product evaluator. The result is a pair of the
modulus and the complementary product modulo it. At a valid indexed-system
query, this is exactly the cofactor from the CRT reconstruction specification.
-/

@[expose] public section

namespace LeanCanny.Algebra.ChineseRemainder.CofactorBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open scoped BigOperators

theorem indexedModulus_pos (N i : ℕ) : 0 < indexedModulus N i := by
  unfold indexedModulus
  split_ifs with hp
  · exact pow_pos hp.pos _
  · decide

theorem product_eq_cofactor (N : ℕ) (i : Fin (N + 1)) :
    product N i.val (N + 1) = (indexedSystem N).cofactor i := by
  rw [product, Finset.prod_range]
  calc
    _ = ∏ j : Fin (N + 1), if j ∈ Finset.univ.erase i then indexedModulus N j.val else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases he : j = i
      · subst j
        simp
      · have hn : j.val ≠ i.val := fun h => he (Fin.ext h)
        have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨he, Finset.mem_univ j⟩
        rw [ite_eq_right hn, ite_eq_left hj]
    _ = ∏ j ∈ Finset.univ.erase i, indexedModulus N j.val := Finset.prod_ite_mem_eq _ _
    _ = _ := rfl

theorem product_coprime (N : ℕ) (i : Fin (N + 1)) :
    (product N i.val (N + 1)).Coprime (indexedModulus N i.val) := by
  rw [product_eq_cofactor]
  exact (indexedSystem N).cofactor_coprime i

def install (z : List Bool) : List Bool := pair (pairFst z) (BinaryNat.pred (pairSnd z))
def collect (z : List Bool) : List Bool := pair (BinaryNat.succ (pairSnd (pairFst z))) (pairSnd z)
def value (c : List Bool) : List Bool :=
  let N := Nat.fromBitsLE (pairFst c)
  let i := Nat.fromBitsLE (pairSnd c)
  pair (BinaryNatCode.encode (indexedModulus N i))
    (BinaryNatCode.encode (product N i (N + 1) % indexedModulus N i))

theorem install_mem_FP : install ∈ FP := by
  have hp := mem_FP_comp pairSnd_mem_FP BinaryNat.pred_mem_FP
  have h := mem_FP_pair pairFst_mem_FP hp
  refine mem_FP_of_eq (g := install) h ?_
  intro z
  simp only [Function.comp_apply, install]

theorem collect_mem_FP : collect ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.succ_mem_FP
  have h := mem_FP_pair hm pairSnd_mem_FP
  refine mem_FP_of_eq (g := collect) h ?_
  intro z
  simp only [Function.comp_apply, collect]

noncomputable def evaluator : SpaceFunction value := by
  let M := ModulusBits.evaluator.withInput.postcompose install install_mem_FP
  let P := productEvaluator.withInput.postcompose collect collect_mem_FP
  let E := M.chain P
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, install, collect, source, target, pairFst_pair, pairSnd_pair,
    BinaryNat.pred_eq_bits, BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, value]
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (indexedModulus_pos _ _).ne')]

theorem value_pair (N : ℕ) (i : Fin (N + 1)) :
    value (pair (BinaryNatCode.encode N) (BinaryNatCode.encode i.val)) =
      pair (BinaryNatCode.encode ((indexedSystem N).modulus i))
        (BinaryNatCode.encode ((indexedSystem N).cofactor i % (indexedSystem N).modulus i)) := by
  simp only [value, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, product_eq_cofactor]
  rfl

end LeanCanny.Algebra.ChineseRemainder.CofactorBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CofactorResidueSpace
public import LeanCanny.Algebra.ModularInverseSpace

/-!
# Certified local CRT weights

Compute the selected modulus and complementary-product residue, then search for
its modular inverse. The cofactor-coprimality theorem proves that, at every valid
indexed-system query, the result is exactly the inverse used by the CRT sum.
-/

@[expose] public section

namespace LeanCanny.Algebra.ChineseRemainder.WeightBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation

def inverseQuery (z : List Bool) : List Bool := pair (pairSnd z) (BinaryNat.pred (pairFst z))
def finish (z : List Bool) : List Bool := pair (pairFst (pairFst z)) (pairSnd z)
def value (q : List Bool) : List Bool :=
  let p := CofactorBits.value q
  pair (pairFst p) (ModularInverseBits.value (inverseQuery p))

theorem inverseQuery_mem_FP : inverseQuery ∈ FP := by
  have hm := mem_FP_comp pairFst_mem_FP BinaryNat.pred_mem_FP
  have h := mem_FP_pair pairSnd_mem_FP hm
  refine mem_FP_of_eq (g := inverseQuery) h ?_
  intro z
  simp only [Function.comp_apply, inverseQuery]

theorem finish_mem_FP : finish ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

noncomputable def evaluator : SpaceFunction value := by
  let I := ((ModularInverseBits.evaluator.precompose inverseQuery inverseQuery_mem_FP).withInput).postcompose finish finish_mem_FP
  let E := CofactorBits.evaluator.chain I
  refine E.congr (funext fun q => ?_)
  simp only [Function.comp_apply, finish, pairFst_pair, pairSnd_pair, value]

theorem value_pair (N : ℕ) (i : Fin (N + 1)) :
    value (pair (BinaryNatCode.encode N) (BinaryNatCode.encode i.val)) =
      pair (BinaryNatCode.encode ((indexedSystem N).modulus i)) (BinaryNatCode.encode ((indexedSystem N).inverse i)) := by
  let F := indexedSystem N
  let M := F.modulus i
  let C := F.cofactor i
  have hM : 0 < M := F.positive i
  have hco : (C % M).Coprime M := by
    change Nat.gcd (C % M) M = 1
    have h : Nat.gcd M C = 1 := (F.cofactor_coprime i).symm
    rw [Nat.gcd_rec] at h
    exact h
  rw [value, CofactorBits.value_pair, pairFst_pair]
  change pair (BinaryNatCode.encode M)
    (ModularInverseBits.value (inverseQuery (pair (BinaryNatCode.encode M) (BinaryNatCode.encode (C % M))))) = _
  have hq : inverseQuery (pair (BinaryNatCode.encode M) (BinaryNatCode.encode (C % M))) =
      pair (BinaryNatCode.encode (C % M)) (BinaryNatCode.encode (M - 1)) := by
    simp only [inverseQuery, pairFst_pair, pairSnd_pair, BinaryNat.pred_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [hq, ModularInverseBits.value_pair (C % M) M hM hco]
  simp only [ZMod.natCast_mod]
  rfl

end LeanCanny.Algebra.ChineseRemainder.WeightBits

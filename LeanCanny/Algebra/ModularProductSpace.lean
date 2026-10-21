/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ModularSumSpace

/-! # Streamed modular products with space-bounded factor evaluation

Reduce the accumulator after every multiplication. Binary count and modulus
fields allow exponentially many factors while keeping the parent short.
The complete child computations and the empty product are included.
-/

@[expose] public section

namespace LeanCanny.Algebra.ModularProduct

open LeanCanny.Encoding LeanCanny.Computation
open MatrixPower
open scoped BigOperators

def seed (modulus : List Bool → List Bool) (c : List Bool) : List Bool := ArithmeticBits.one (modulus c)
def finish (modulus : List Bool → List Bool) (z : List Bool) : List Bool :=
  BinaryNat.mod (pair (BinaryNat.mul (pair (BoundedFold.accumulator (pairFst z)) (pairSnd z)))
    (modulus (pairFst (pairFst z))))
def update (modulus f : List Bool → List Bool) (p : List Bool) : List Bool :=
  finish modulus (pair p (f (ModularSum.query p)))

theorem seed_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : seed modulus ∈ FP :=
  mem_FP_comp hm ArithmeticBits.one_mem_FP

theorem finish_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : finish modulus ∈ FP := by
  have hv := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP) pairSnd_mem_FP)
    BinaryNat.mul_mem_FP
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have h := mem_FP_comp (mem_FP_pair hv (mem_FP_comp hc hm)) BinaryNat.mod_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem updateEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (modulus : List Bool → List Bool) (hm : modulus ∈ FP) : SpaceFunction (update modulus f) := by
  let Q := (E.precompose ModularSum.query ModularSum.query_mem_FP).withInput.postcompose (finish modulus) (finish_mem_FP hm)
  exact Q.congr (funext fun _ => rfl)

theorem fold_eq_product (modulus f : List Bool → List Bool) (c : List Bool) (N : ℕ)
    (a : ℕ → ZMod (Nat.fromBitsLE (modulus c))) (hm : 0 < Nat.fromBitsLE (modulus c))
    (hf : ∀ i < N, f (pair c (BinaryNatCode.encode i)) = residueBits (a i)) (k : ℕ) (hk : k ≤ N) :
    BoundedFold.fold (update modulus f) (seed modulus) c k = residueBits (∏ i ∈ Finset.range k, a i) := by
  let : NeZero (Nat.fromBitsLE (modulus c)) := ⟨hm.ne'⟩
  induction k with
  | zero =>
    simp only [BoundedFold.fold, seed, Finset.range_zero, Finset.prod_empty, ArithmeticBits.one, BinaryNat.mod_pair,
      residueBits, BinaryNatCode.encode, ZMod.val_one_eq_one_mod]
    rfl
  | succ k ih =>
    rw [BoundedFold.fold, ih (by omega), Finset.prod_range_succ]
    rw [update, ModularSum.query, BoundedFold.context_packet, BoundedFold.counter_packet, hf k (by omega)]
    simp only [finish, pairFst_pair, pairSnd_pair, BoundedFold.accumulator_packet, BoundedFold.context_packet, BinaryNat.mod_pair,
      BinaryNat.mul_pair, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_mul]

theorem evaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count modulus : List Bool → List Bool) (hc : count ∈ FP) (hm : modulus ∈ FP)
    (a : (c : List Bool) → ℕ → ZMod (Nat.fromBitsLE (modulus c)))
    (hpos : ∀ c, 0 < Nat.fromBitsLE (modulus c))
    (hf : ∀ c i, i < Nat.fromBitsLE (count c) → f (pair c (BinaryNatCode.encode i)) = residueBits (a c i)) :
    SpaceFunction (fun c => residueBits (∏ i ∈ Finset.range (Nat.fromBitsLE (count c)), a c i)) := by
  let p := Classical.choose (output_length_poly_of_mem_FP hm)
  have hp : ∀ c, (modulus c).length ≤ p.eval c.length := Classical.choose_spec (output_length_poly_of_mem_FP hm)
  have hs : ∀ c k, k ≤ Nat.fromBitsLE (count c) →
      (BoundedFold.fold (update modulus f) (seed modulus) c k).length ≤ p.eval c.length := by
    intro c k hk
    let : NeZero (Nat.fromBitsLE (modulus c)) := ⟨(hpos c).ne'⟩
    rw [fold_eq_product modulus f c _ (a c) (hpos c) (hf c) k hk, residueBits, BinaryNatCode.length_encode]
    exact (Nat.size_le.mpr ((ZMod.val_lt _).trans (Nat.fromBitsLE_lt_pow_length (modulus c)))).trans (hp c)
  let Q := BoundedFold.evaluator (updateEvaluator E modulus hm) count (seed modulus) hc (seed_mem_FP hm) p hs
  exact Q.congr (funext fun c => fold_eq_product modulus f c _ (a c) (hpos c) (hf c) _ le_rfl)

theorem evaluatorWithModulus {f : List Bool → List Bool} (E : SpaceFunction f)
    (count modulus : List Bool → List Bool) (hc : count ∈ FP) (hm : modulus ∈ FP)
    (m : List Bool → ℕ) (hvalue : (fun c => Nat.fromBitsLE (modulus c)) = m)
    (a : (c : List Bool) → ℕ → ZMod (m c)) (hpos : ∀ c, 0 < m c)
    (hf : ∀ c i, i < Nat.fromBitsLE (count c) →
      f (pair c (BinaryNatCode.encode i)) = residueBits (a c i)) :
    SpaceFunction (fun c => residueBits (∏ i ∈ Finset.range (Nat.fromBitsLE (count c)), a c i)) := by
  subst m
  exact evaluator E count modulus hc hm a hpos hf

end LeanCanny.Algebra.ModularProduct

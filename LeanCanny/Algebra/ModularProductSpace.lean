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
  ModularFold.finish BinaryNat.mul modulus z

def update (modulus f : List Bool → List Bool) (p : List Bool) : List Bool :=
  BoundedFold.update (finish modulus) f p

theorem seed_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : seed modulus ∈ FP :=
  mem_FP_comp hm ArithmeticBits.one_mem_FP

theorem finish_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : finish modulus ∈ FP :=
  ModularFold.finish_mem_FP BinaryNat.mul_mem_FP hm

theorem updateEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (modulus : List Bool → List Bool) (hm : modulus ∈ FP) : SpaceFunction (update modulus f) := by
  exact BoundedFold.updateEvaluator E (finish modulus) (finish_mem_FP hm)

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
    rw [update, BoundedFold.update, BoundedFold.query, BoundedFold.context_packet, BoundedFold.counter_packet, hf k (by omega)]
    simp only [finish, ModularFold.finish, pairFst_pair, pairSnd_pair, BoundedFold.accumulator_packet, BoundedFold.context_packet, BinaryNat.mod_pair,
      BinaryNat.mul_pair, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_mul]

theorem evaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count modulus : List Bool → List Bool) (hc : count ∈ FP) (hm : modulus ∈ FP)
    (a : (c : List Bool) → ℕ → ZMod (Nat.fromBitsLE (modulus c)))
    (hpos : ∀ c, 0 < Nat.fromBitsLE (modulus c))
    (hf : ∀ c i, i < Nat.fromBitsLE (count c) → f (pair c (BinaryNatCode.encode i)) = residueBits (a c i)) :
    SpaceFunction (fun c => residueBits (∏ i ∈ Finset.range (Nat.fromBitsLE (count c)), a c i)) := by
  exact ModularFold.evaluator_residue (updateEvaluator E modulus hm) count modulus (seed modulus)
    hc hm (seed_mem_FP hm) (fun c k => ∏ i ∈ Finset.range k, a c i) hpos
    (fun c k hk => fold_eq_product modulus f c _ (a c) (hpos c) (hf c) k hk)

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

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ModularFoldSpace
public import LeanCanny.Algebra.MatrixPowerArithmeticFP

/-!
# A streamed modular sum with space-bounded summand evaluation

FP binary fields specify a count and positive modulus. A certified child returns
one canonical summand residue at a time. The accumulator is reduced after every
addition and fits in the modulus word, including for an empty sum and modulus
one. Native space iteration composes each child directly.
-/

@[expose] public section

namespace LeanCanny.Algebra.ModularSum

open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower
open scoped BigOperators

def query (p : List Bool) : List Bool := BoundedFold.query p
def finish (modulus : List Bool → List Bool) (z : List Bool) : List Bool :=
  ModularFold.finish BinaryNat.add modulus z

def update (modulus f : List Bool → List Bool) (p : List Bool) : List Bool :=
  BoundedFold.update (finish modulus) f p

theorem query_mem_FP : query ∈ FP := BoundedFold.query_mem_FP

theorem finish_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : finish modulus ∈ FP :=
  ModularFold.finish_mem_FP BinaryNat.add_mem_FP hm

theorem updateEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (modulus : List Bool → List Bool) (hm : modulus ∈ FP) : SpaceFunction (update modulus f) := by
  exact BoundedFold.updateEvaluator E (finish modulus) (finish_mem_FP hm)

theorem update_packet (modulus f : List Bool → List Bool) (c : List Bool) (i : ℕ)
    (hm : 0 < Nat.fromBitsLE (modulus c)) (a v : ZMod (Nat.fromBitsLE (modulus c)))
    (hf : f (pair c (BinaryNatCode.encode i)) = residueBits a) :
    update modulus f (BoundedFold.packet c i (residueBits v)) = residueBits (v + a) := by
  let : NeZero (Nat.fromBitsLE (modulus c)) := ⟨hm.ne'⟩
  simp only [update, BoundedFold.update, BoundedFold.query, BoundedFold.context_packet, BoundedFold.counter_packet, hf]
  simp only [finish, ModularFold.finish, pairFst_pair, pairSnd_pair, BoundedFold.context_packet, BoundedFold.accumulator_packet, BinaryNat.mod_pair,
    BinaryNat.add_pair, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_add]

theorem fold_eq_sum (modulus f : List Bool → List Bool) (c : List Bool) (N : ℕ)
    (a : ℕ → ZMod (Nat.fromBitsLE (modulus c))) (hm : 0 < Nat.fromBitsLE (modulus c))
    (hf : ∀ i, i < N → f (pair c (BinaryNatCode.encode i)) = residueBits (a i)) (k : ℕ) (hk : k ≤ N) :
    BoundedFold.fold (update modulus f) (fun _ => []) c k = residueBits (∑ i ∈ Finset.range k, a i) := by
  induction k with
  | zero => simp [BoundedFold.fold, residueBits, BinaryNatCode.encode]
  | succ k ih =>
    rw [BoundedFold.fold, ih (by omega), update_packet modulus f c k hm _ _ (hf k (by omega)), Finset.sum_range_succ]

theorem evaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count modulus : List Bool → List Bool) (hc : count ∈ FP) (hm : modulus ∈ FP)
    (a : (c : List Bool) → ℕ → ZMod (Nat.fromBitsLE (modulus c)))
    (hpos : ∀ c, 0 < Nat.fromBitsLE (modulus c))
    (hf : ∀ c i, i < Nat.fromBitsLE (count c) →
      f (pair c (BinaryNatCode.encode i)) = residueBits (a c i)) :
    SpaceFunction (fun c => residueBits (∑ i ∈ Finset.range (Nat.fromBitsLE (count c)), a c i)) := by
  exact ModularFold.evaluator_residue (updateEvaluator E modulus hm) count modulus (fun _ => [])
    hc hm (constFn_mem_FP []) (fun c k => ∑ i ∈ Finset.range k, a c i) hpos
    (fun c k hk => fold_eq_sum modulus f c _ (a c) (hpos c) (hf c) k hk)

theorem evaluatorWithModulus {f : List Bool → List Bool} (E : SpaceFunction f)
    (count modulus : List Bool → List Bool) (hc : count ∈ FP) (hm : modulus ∈ FP)
    (m : List Bool → ℕ) (hvalue : (fun c => Nat.fromBitsLE (modulus c)) = m)
    (a : (c : List Bool) → ℕ → ZMod (m c)) (hpos : ∀ c, 0 < m c)
    (hf : ∀ c i, i < Nat.fromBitsLE (count c) →
      f (pair c (BinaryNatCode.encode i)) = residueBits (a c i)) :
    SpaceFunction (fun c => residueBits (∑ i ∈ Finset.range (Nat.fromBitsLE (count c)), a c i)) := by
  subst m
  exact evaluator E count modulus hc hm a hpos hf

end LeanCanny.Algebra.ModularSum

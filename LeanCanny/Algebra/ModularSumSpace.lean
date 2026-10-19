/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFoldSpace
public import LeanCanny.Algebra.MatrixPowerArithmeticFP

/-!
# A streamed modular sum with suspended summand evaluation

FP binary fields specify a count and positive modulus. A certified child returns
one canonical summand residue at a time. The accumulator is reduced after every
addition and fits in the modulus word, including for an empty sum and modulus
one. The full evaluator counts saved parent and child states and the call clock.
-/

@[expose] public section

namespace LeanCanny.Algebra.ModularSum
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower
open scoped BigOperators

def query (p : List Bool) : List Bool := pair (pairFst p) (BoundedFold.counter p)
def finish (modulus : List Bool → List Bool) (z : List Bool) : List Bool :=
  BinaryNat.mod (pair (BinaryNat.add (pair (BoundedFold.accumulator (pairFst z)) (pairSnd z)))
    (modulus (pairFst (pairFst z))))
def update (modulus f : List Bool → List Bool) (p : List Bool) : List Bool := finish modulus (pair p (f (query p)))

theorem query_mem_FP : query ∈ FP := mem_FP_pair pairFst_mem_FP BoundedFold.counter_mem_FP

theorem finish_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : finish modulus ∈ FP := by
  have ha := mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hs := mem_FP_comp (mem_FP_pair ha pairSnd_mem_FP) BinaryNat.add_mem_FP
  have h := mem_FP_comp (mem_FP_pair hs (mem_FP_comp hc hm)) BinaryNat.mod_mem_FP
  refine mem_FP_of_eq (g := finish modulus) h ?_
  intro z
  simp only [Function.comp_apply, finish]

noncomputable def updateEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (modulus : List Bool → List Bool) (hm : modulus ∈ FP) : SpaceFunction (update modulus f) := by
  let Q := ((E.precompose query query_mem_FP).withInput).postcompose (finish modulus) (finish_mem_FP hm)
  refine Q.congr (funext fun p => ?_)
  simp only [Function.comp_apply, update]

theorem update_packet (modulus f : List Bool → List Bool) (c : List Bool) (i : ℕ)
    (hm : 0 < Nat.fromBitsLE (modulus c)) (a v : ZMod (Nat.fromBitsLE (modulus c)))
    (hf : f (pair c (BinaryNatCode.encode i)) = residueBits a) :
    update modulus f (BoundedFold.packet c i (residueBits v)) = residueBits (v + a) := by
  let : NeZero (Nat.fromBitsLE (modulus c)) := ⟨hm.ne'⟩
  simp only [update, query, BoundedFold.context_packet, BoundedFold.counter_packet, hf]
  simp only [finish, pairFst_pair, pairSnd_pair, BoundedFold.context_packet, BoundedFold.accumulator_packet, BinaryNat.mod_pair,
    BinaryNat.add_pair, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_add]

theorem fold_eq_sum (modulus f : List Bool → List Bool) (c : List Bool) (N : ℕ)
    (a : ℕ → ZMod (Nat.fromBitsLE (modulus c))) (hm : 0 < Nat.fromBitsLE (modulus c))
    (hf : ∀ i, i < N → f (pair c (BinaryNatCode.encode i)) = residueBits (a i)) (k : ℕ) (hk : k ≤ N) :
    BoundedFold.fold (update modulus f) (fun _ => []) c k = residueBits (∑ i ∈ Finset.range k, a i) := by
  induction k with
  | zero => simp [BoundedFold.fold, residueBits, BinaryNatCode.encode]
  | succ k ih =>
    rw [BoundedFold.fold, ih (by omega), update_packet modulus f c k hm _ _ (hf k (by omega)), Finset.sum_range_succ]

noncomputable def evaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count modulus : List Bool → List Bool) (hc : count ∈ FP) (hm : modulus ∈ FP)
    (a : (c : List Bool) → ℕ → ZMod (Nat.fromBitsLE (modulus c)))
    (hpos : ∀ c, 0 < Nat.fromBitsLE (modulus c))
    (hf : ∀ c i, i < Nat.fromBitsLE (count c) →
      f (pair c (BinaryNatCode.encode i)) = residueBits (a c i)) :
    SpaceFunction (fun c => residueBits (∑ i ∈ Finset.range (Nat.fromBitsLE (count c)), a c i)) := by
  let p := Classical.choose (Cobham.output_length_poly_of_mem_FP hm)
  have hp : ∀ c, (modulus c).length ≤ p.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hm)
  have hstate : ∀ c k, k ≤ Nat.fromBitsLE (count c) →
      (BoundedFold.fold (update modulus f) (fun _ => []) c k).length ≤ p.eval c.length := by
    intro c k hk
    let : NeZero (Nat.fromBitsLE (modulus c)) := ⟨(hpos c).ne'⟩
    rw [fold_eq_sum modulus f c _ (a c) (hpos c) (hf c) k hk, residueBits, BinaryNatCode.length_encode]
    apply (Nat.size_le.mpr ?_).trans (hp c)
    exact (ZMod.val_lt (∑ i ∈ Finset.range k, a c i)).trans (Nat.fromBitsLE_lt_pow_length (modulus c))
  let Q := BoundedFold.evaluator (updateEvaluator E modulus hm) count (fun _ => []) hc (constFn_mem_FP []) p hstate
  exact Q.congr (funext fun c => fold_eq_sum modulus f c _ (a c) (hpos c) (hf c) _ le_rfl)

noncomputable def evaluatorWithModulus {f : List Bool → List Bool} (E : SpaceFunction f)
    (count modulus : List Bool → List Bool) (hc : count ∈ FP) (hm : modulus ∈ FP)
    (m : List Bool → ℕ) (hvalue : (fun c => Nat.fromBitsLE (modulus c)) = m)
    (a : (c : List Bool) → ℕ → ZMod (m c)) (hpos : ∀ c, 0 < m c)
    (hf : ∀ c i, i < Nat.fromBitsLE (count c) →
      f (pair c (BinaryNatCode.encode i)) = residueBits (a c i)) :
    SpaceFunction (fun c => residueBits (∑ i ∈ Finset.range (Nat.fromBitsLE (count c)), a c i)) := by
  subst m
  exact evaluator E count modulus hc hm a hpos hf

end LeanCanny.Algebra.ModularSum

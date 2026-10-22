/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IndexedModulusSpace
public import LeanCanny.Encoding.BinaryPowModFP

/-!
# Streamed complementary products of CRT moduli

The inner context is `pair (pair N i) (m-1)`. A bounded fold multiplies the
indexed moduli, replacing factor `i` by one and reducing after every product.
Each factor is computed by the certified indexed-modulus evaluator. The
positive-modulus protocol bounds every accumulator, including on raw inputs.
-/

@[expose] public section

namespace LeanCanny.Algebra.ChineseRemainder.CofactorBits

open LeanCanny.Encoding
open LeanCanny.Computation
open scoped BigOperators

def product (N i k : ℕ) : ℕ := ∏ j ∈ Finset.range k, if j = i then 1 else indexedModulus N j

def source (c : List Bool) : List Bool := pairFst (pairFst c)
def target (c : List Bool) : List Bool := pairSnd (pairFst c)
def modulus (c : List Bool) : List Bool := BinaryNat.succ (pairSnd c)
def query (p : List Bool) : List Bool := pair (source (pairFst p)) (BoundedFold.counter p)
def skip (z : List Bool) : Prop :=
  Nat.fromBitsLE (BoundedFold.counter (pairFst z)) = Nat.fromBitsLE (target (pairFst (pairFst z)))
instance (z : List Bool) : Decidable (skip z) := inferInstanceAs (Decidable (_ = _))
def chosenFactor (z : List Bool) : List Bool := if skip z then [true] else pairSnd z
def finish (z : List Bool) : List Bool := BinaryNat.mulMod
  (pair (modulus (pairFst (pairFst z))) (pair (BoundedFold.accumulator (pairFst z)) (chosenFactor z)))
def update (p : List Bool) : List Bool := finish (pair p (BinaryNatCode.encode
  (indexedModulus (Nat.fromBitsLE (source (pairFst p))) (Nat.fromBitsLE (BoundedFold.counter p)))))
def seed (c : List Bool) : List Bool := BinaryNat.mod (pair [true] (modulus c))

theorem source_mem_FP : source ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem target_mem_FP : target ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem modulus_mem_FP : modulus ∈ FP := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
theorem query_mem_FP : query ∈ FP := by
  have h := mem_FP_pair (mem_FP_comp pairFst_mem_FP source_mem_FP) BoundedFold.counter_mem_FP
  refine mem_FP_of_eq (g := query) h ?_
  intro p
  simp only [Function.comp_apply, query]

theorem skip_fppred : FPPred skip := by
  have hj := mem_FP_comp pairFst_mem_FP BoundedFold.counter_mem_FP
  have hi := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) target_mem_FP
  refine ((BinaryNat.le_fppred hj hi).and (BinaryNat.le_fppred hi hj)).of_iff ?_
  intro z
  dsimp only [skip, Function.comp_apply]
  omega

theorem chosenFactor_mem_FP : chosenFactor ∈ FP :=
  skip_fppred.ite_mem_FP (constFn_mem_FP [true]) pairSnd_mem_FP

theorem finish_mem_FP : finish ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) modulus_mem_FP
  have ha := mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP
  have h := mem_FP_comp (mem_FP_pair hm (mem_FP_pair ha chosenFactor_mem_FP)) BinaryNat.mulMod_mem_FP
  refine mem_FP_of_eq (g := finish) h ?_
  intro z
  simp only [Function.comp_apply, finish]

theorem seed_mem_FP : seed ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (constFn_mem_FP [true]) modulus_mem_FP) BinaryNat.mod_mem_FP
  refine mem_FP_of_eq (g := seed) h ?_
  intro c
  simp only [Function.comp_apply, seed]

theorem updateEvaluator : SpaceFunction update := by
  let E := ((ModulusBits.evaluator.precompose query query_mem_FP).withInput).postcompose finish finish_mem_FP
  refine E.congr (funext fun p => ?_)
  simp only [Function.comp_apply, query, pairFst_pair, pairSnd_pair, update]

theorem seed_eq (c : List Bool) : seed c = (1 % (Nat.fromBitsLE (pairSnd c) + 1)).bits := by
  simp only [seed, modulus, BinaryNat.mod_pair, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits,
    show Nat.fromBitsLE [true] = 1 from rfl]

theorem update_packet (c : List Bool) (j v : ℕ) : update (BoundedFold.packet c j v.bits) =
    (v * (if j = Nat.fromBitsLE (target c) then 1 else indexedModulus (Nat.fromBitsLE (source c)) j) %
      (Nat.fromBitsLE (pairSnd c) + 1)).bits := by
  simp only [update, BoundedFold.context_packet, BoundedFold.counter_packet,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  simp only [finish, chosenFactor, skip, pairFst_pair, pairSnd_pair, BoundedFold.context_packet,
    BoundedFold.counter_packet, BoundedFold.accumulator_packet, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    modulus, BinaryNat.succ_eq_bits]
  split_ifs <;> simp only [BinaryNat.mulMod_pair, Nat.fromBitsLE_bits, show Nat.fromBitsLE [true] = 1 from rfl]

theorem fold_eq (c : List Bool) (k : ℕ) : BoundedFold.fold update seed c k =
    (product (Nat.fromBitsLE (source c)) (Nat.fromBitsLE (target c)) k % (Nat.fromBitsLE (pairSnd c) + 1)).bits := by
  induction k with
  | zero => simpa only [BoundedFold.fold, product, Finset.range_zero, Finset.prod_empty] using seed_eq c
  | succ k ih =>
    rw [BoundedFold.fold, ih, update_packet]
    simp only [product, Finset.prod_range_succ, Nat.mul_mod, Nat.mod_mod]

theorem productEvaluator : SpaceFunction (fun c =>
    (product (Nat.fromBitsLE (source c)) (Nat.fromBitsLE (target c)) (Nat.fromBitsLE (source c) + 1) %
      (Nat.fromBitsLE (pairSnd c) + 1)).bits) := by
  have hb := mem_FP_comp source_mem_FP BinaryNat.succ_mem_FP
  have hs : ∀ c k, k ≤ Nat.fromBitsLE ((BinaryNat.succ ∘ source) c) →
      (BoundedFold.fold update seed c k).length ≤ (Polynomial.X : Polynomial ℕ).eval c.length := by
    intro c k _
    rw [fold_eq, Nat.size_eq_bits_len]
    have hr := Nat.mod_lt (product (Nat.fromBitsLE (source c)) (Nat.fromBitsLE (target c)) k)
      (by omega : 0 < Nat.fromBitsLE (pairSnd c) + 1)
    have hraw := (Nat.fromBitsLE_lt_pow_length (pairSnd c)).trans_le
      (Nat.pow_le_pow_right (by decide) (pairSnd_length_le c))
    exact Nat.size_le.mpr (by simpa only [Polynomial.eval_X] using (by omega :
      product (Nat.fromBitsLE (source c)) (Nat.fromBitsLE (target c)) k %
        (Nat.fromBitsLE (pairSnd c) + 1) < 2 ^ c.length))
  let E := BoundedFold.evaluator updateEvaluator (BinaryNat.succ ∘ source) seed hb seed_mem_FP Polynomial.X hs
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, fold_eq]

end LeanCanny.Algebra.ChineseRemainder.CofactorBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionChain
public import LeanCanny.Computation.BoundedFoldSpace

/-! # Streaming a bounded maximum in polynomial space

A binary count permits exponentially many calls to a certified natural-value
reader. The maximum accumulator fits in the supplied binary value allowance.
The certificate accounts for saved parent states and every child computation.
-/

@[expose] public section

namespace LeanCanny.Computation.BoundedMaximum
open Complexity
open LeanCanny.Encoding

def maximum (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairFst p) ≤ Nat.fromBitsLE (pairSnd p) then pairSnd p else pairFst p

theorem maximum_mem_FP : maximum ∈ FP :=
  (BinaryNat.le_fppred pairFst_mem_FP pairSnd_mem_FP).ite_mem_FP pairSnd_mem_FP pairFst_mem_FP

theorem maximum_codes (a b : ℕ) : maximum (pair (BinaryNatCode.encode a) (BinaryNatCode.encode b)) =
    BinaryNatCode.encode (max a b) := by
  simp only [maximum, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs with h
  · rw [max_eq_right h]
  · rw [max_eq_left (by omega)]

def query (p : List Bool) : List Bool := pair (pairFst p) (BoundedFold.counter p)
def finish (z : List Bool) : List Bool := maximum (pair (BoundedFold.accumulator (pairFst z)) (pairSnd z))
def update (f : List Bool → List Bool) (p : List Bool) : List Bool := finish (pair p (f (query p)))

theorem query_mem_FP : query ∈ FP := mem_FP_pair pairFst_mem_FP BoundedFold.counter_mem_FP
theorem finish_mem_FP : finish ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP) pairSnd_mem_FP) maximum_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem updateEvaluator {f : List Bool → List Bool} (E : SpaceFunction f) : SpaceFunction (update f) := by
  let Q := (E.precompose query query_mem_FP).withInput.postcompose finish finish_mem_FP
  exact Q.congr (funext fun _ => rfl)

theorem fold_eq_maximum (f : List Bool → List Bool) (c : List Bool) (N : ℕ) (a : ℕ → ℕ)
    (hf : ∀ i < N, f (pair c (BinaryNatCode.encode i)) = BinaryNatCode.encode (a i))
    (k : ℕ) (hk : k ≤ N) :
    BoundedFold.fold (update f) (fun _ => []) c k = BinaryNatCode.encode ((Finset.range k).sup a) := by
  induction k with
  | zero => simp [BoundedFold.fold, BinaryNatCode.encode]
  | succ k ih =>
    rw [BoundedFold.fold, ih (by omega)]
    simp only [update, query, BoundedFold.context_packet, BoundedFold.counter_packet, hf k (by omega),
      finish, pairFst_pair, pairSnd_pair, BoundedFold.accumulator_packet, maximum_codes]
    rw [Finset.range_add_one, Finset.sup_insert]
    exact congrArg BinaryNatCode.encode (max_comm _ _)

theorem evaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count bound : List Bool → List Bool) (hc : count ∈ FP) (hb : bound ∈ FP)
    (a : List Bool → ℕ → ℕ)
    (hf : ∀ c i, i < Nat.fromBitsLE (count c) → f (pair c (BinaryNatCode.encode i)) = BinaryNatCode.encode (a c i))
    (hbound : ∀ c i, i < Nat.fromBitsLE (count c) → a c i ≤ Nat.fromBitsLE (bound c)) :
    SpaceFunction (fun c => BinaryNatCode.encode ((Finset.range (Nat.fromBitsLE (count c))).sup (a c))) := by
  let p := Classical.choose (Cobham.output_length_poly_of_mem_FP hb)
  have hp : ∀ c, (bound c).length ≤ p.eval c.length := Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hb)
  have hs : ∀ c k, k ≤ Nat.fromBitsLE (count c) →
      (BoundedFold.fold (update f) (fun _ => []) c k).length ≤ p.eval c.length := by
    intro c k hk
    rw [fold_eq_maximum f c _ (a c) (hf c) k hk, BinaryNatCode.length_encode]
    have hm : (Finset.range k).sup (a c) ≤ Nat.fromBitsLE (bound c) :=
      Finset.sup_le (fun i hi => hbound c i (by have := Finset.mem_range.mp hi; omega))
    apply (Nat.size_le.mpr ?_).trans (hp c)
    exact hm.trans_lt (Nat.fromBitsLE_lt_pow_length (bound c))
  let Q := BoundedFold.evaluator (updateEvaluator E) count (fun _ => []) hc (constFn_mem_FP []) p hs
  exact Q.congr (funext fun c => fold_eq_maximum f c _ (a c) (hf c) _ le_rfl)

end LeanCanny.Computation.BoundedMaximum

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerSumSpace

/-! # Space-bounded products of small signed factors

Factors have absolute value at most two. A unary FP bound on their count keeps
the full product's binary representation polynomial in the original input.
Factor evaluation may itself use polynomial space.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerSmallProductBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open scoped BigOperators

def product (a : ℕ → ℤ) (n : ℕ) : ℤ := ∏ i ∈ Finset.range n, a i

theorem product_abs_le (a : ℕ → ℤ) (ha : ∀ i, (a i).natAbs ≤ 2) (n : ℕ) :
    (product a n).natAbs ≤ 2 ^ n := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    simp only [product, Finset.prod_range_succ, Int.natAbs_mul, pow_succ]
    exact Nat.mul_le_mul ih (ha n)

theorem code_length_le (z : ℤ) (n : ℕ) (hz : z.natAbs ≤ 2 ^ n) :
    (SignStatisticBits.integerCode z).length ≤ 3 * n + 5 := by
  have ht : z.toNat + (-z).toNat ≤ 2 ^ n := by
    rw [Int.toNat_add_toNat_neg_eq_natAbs]
    exact hz
  have hp : z.toNat.size ≤ n + 1 := by
    simpa only [Nat.size_pow] using Nat.size_le_size (show z.toNat ≤ 2 ^ n by omega)
  have hn : (-z).toNat.size ≤ n + 1 := by
    simpa only [Nat.size_pow] using Nat.size_le_size (show (-z).toNat ≤ 2 ^ n by omega)
  simp only [SignStatisticBits.integerCode, pair_length, BinaryNatCode.length_encode]
  omega

def finish (z : List Bool) : List Bool :=
  IntegerSumBits.multiply (pair (BoundedFold.accumulator (pairFst z)) (pairSnd z))
def update (f : List Bool → List Bool) (p : List Bool) : List Bool :=
  finish (pair p (f (IntegerSumBits.query p)))

theorem finish_mem_FP : finish ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP)
    pairSnd_mem_FP) IntegerSumBits.multiply_mem_FP
  refine mem_FP_of_eq (g := finish) h ?_
  intro z
  simp only [finish, Function.comp_apply]

noncomputable def updateEvaluator {f : List Bool → List Bool} (E : SpaceFunction f) :
    SpaceFunction (update f) := by
  let Q := (E.precompose IntegerSumBits.query IntegerSumBits.query_mem_FP).withInput.postcompose finish finish_mem_FP
  refine Q.congr (funext fun p => ?_)
  simp only [update, Function.comp_apply]

theorem fold_eq_product (f : List Bool → List Bool) (c : List Bool) (a : ℕ → ℤ)
    (hf : ∀ i, f (pair c (BinaryNatCode.encode i)) = SignStatisticBits.integerCode (a i)) (n : ℕ) :
    BoundedFold.fold (update f) (fun _ => SignStatisticBits.integerCode 1) c n =
      SignStatisticBits.integerCode (product a n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [BoundedFold.fold, ih]
    simp only [update, IntegerSumBits.query, finish, pairFst_pair, pairSnd_pair,
      BoundedFold.context_packet, BoundedFold.counter_packet, BoundedFold.accumulator_packet, hf,
      IntegerSumBits.multiply_codes, product, Finset.prod_range_succ]

noncomputable def evaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count : List Bool → List Bool) (hc : count ∈ FP)
    (hu : UnaryFn (fun c => Nat.fromBitsLE (count c))) (a : List Bool → ℕ → ℤ)
    (hf : ∀ c i, f (pair c (BinaryNatCode.encode i)) = SignStatisticBits.integerCode (a c i))
    (ha : ∀ c i, (a c i).natAbs ≤ 2) :
    SpaceFunction (fun c => SignStatisticBits.integerCode (product (a c) (Nat.fromBitsLE (count c)))) := by
  let p := Classical.choose (Cobham.output_length_poly_of_mem_FP hu.mem_FP)
  have hp0 : ∀ c, (List.replicate (Nat.fromBitsLE (count c)) true).length ≤ p.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hu.mem_FP)
  have hp : ∀ c, Nat.fromBitsLE (count c) ≤ p.eval c.length := by
    intro c
    simpa only [List.length_replicate] using hp0 c
  let Q := BoundedFold.evaluator (updateEvaluator E) count (fun _ => SignStatisticBits.integerCode 1)
    hc (constFn_mem_FP _) (3 * p + 5) (by
      intro c i hi
      rw [fold_eq_product f c (a c) (hf c)]
      have h := code_length_le (product (a c) i) i (product_abs_le (a c) (ha c) i)
      have hn := hi.trans (hp c)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
      omega)
  refine Q.congr (funext fun c => ?_)
  exact fold_eq_product f c (a c) (hf c) _

end LeanCanny.Algebra.IntegerSmallProductBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SumBitCorrect
public import LeanCanny.Computation.SpaceIteration

/-! # A polynomial-space evaluator for a selected sum bit

FP binary count/index writers and a tidy space-bounded summand-bit reader give
one composed update. The carry invariant bounds every encoded state; native
binary iteration supplies the final output certificate. -/

@[expose] public section

namespace LeanCanny.Computation.SumBits

open LeanCanny.Encoding
open LeanCanny.Algebra
open scoped BigOperators

def value (count index : List Bool → List Bool) (a : List Bool → ℕ → ℕ) (c : List Bool) : List Bool :=
  if (∑ i ∈ Finset.range (Nat.fromBitsLE (count c)), a c i).testBit (Nat.fromBitsLE (index c))
    then [true] else []

theorem evaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count index : List Bool → List Bool) (hc : count ∈ FP) (hi : index ∈ FP)
    (a : List Bool → ℕ → ℕ)
    (hbits : ∀ c i k, i < Nat.fromBitsLE (count c) →
      (f (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false = (a c i).testBit k) :
    SpaceFunction (value count index a) := by
  let N := fun c => Nat.fromBitsLE (count c)
  let K := fun c => Nat.fromBitsLE (index c)
  let L := fun c => K c * (N c + 1) + N c
  let p := Classical.choose (output_length_poly_of_mem_FP (limit_mem_FP hc hi))
  have hp : ∀ c, (limit count index c).length ≤ p.eval c.length :=
    Classical.choose_spec (output_length_poly_of_mem_FP (limit_mem_FP hc hi))
  have hdFP := mem_FP_comp (mem_FP_pair hc hc) BinaryNat.add_mem_FP
  let d := Classical.choose (output_length_poly_of_mem_FP hdFP)
  have hd : ∀ c, ((BinaryNat.add ∘ fun x => pair (count x) (count x)) c).length ≤ d.eval c.length :=
    Classical.choose_spec (output_length_poly_of_mem_FP hdFP)
  let r := 2 * Polynomial.X + 2 * p + d + 4
  let F := step f count
  have hL (c : List Bool) : (L c).size ≤ p.eval c.length := by
    have h := hp c
    rw [limit_code, BinaryNatCode.length_encode] at h
    exact h
  have hdN (c : List Bool) : (2 * N c).size ≤ d.eval c.length := by
    simpa only [Function.comp_apply, BinaryNat.add_eq_bits, pairFst_pair, pairSnd_pair,
      Nat.size_eq_bits_len, two_mul, N] using hd c
  have E' : SpaceFunction (fun c => output (F^[L c] (init c))) := by
    have h := SpaceFunction.iterate (stepEvaluator E hc) init (limit count index)
      init_mem_FP (limit_mem_FP hc hi) r ?_
    · refine (h.postcompose output output_mem_FP).congr (funext fun c => ?_)
      simp only [Function.comp_apply, limit_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      rfl
    · intro c t ht
      rw [limit_code, BinaryNatCode.encode, Nat.fromBitsLE_bits] at ht
      rw [iterate_packet f count c (N c) (a c) rfl (hbits c)]
      simp only [packet, pair_length, BinaryNatCode.length_encode]
      have hs := (Nat.size_le_size ht).trans (hL c)
      have hv := (Nat.size_le_size (BinarySum.carryValue_le (N c) (a c) t)).trans (hdN c)
      simp only [r, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
      omega
  exact E'.congr (funext fun c => output_end f count c (N c) (K c) (a c) rfl (hbits c))

end LeanCanny.Computation.SumBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SumBitCorrect
public import LeanCanny.Computation.SpaceFunctionComposition

/-!
# A polynomial-space evaluator for a selected bit of a sum

FP binary writers supply the number of summands and the selected bit index.
A certified space-bounded routine supplies individual summand bits. The parent
retains only its input, step counter, and accumulator; the suspended-iteration
certificate includes every child state and the expanded physical clock.
-/

@[expose] public section

namespace LeanCanny.Computation.SumBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Algebra
open scoped BigOperators

def value (count index : List Bool → List Bool) (a : List Bool → ℕ → ℕ) (c : List Bool) : List Bool :=
  if (∑ i ∈ Finset.range (Nat.fromBitsLE (count c)), a c i).testBit (Nat.fromBitsLE (index c))
    then [true] else []

noncomputable def evaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count index : List Bool → List Bool) (hc : count ∈ FP) (hi : index ∈ FP)
    (a : List Bool → ℕ → ℕ)
    (hbits : ∀ c i k, i < Nat.fromBitsLE (count c) →
      (f (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false = (a c i).testBit k) :
    SpaceFunction (value count index a) := by
  let N := fun c => Nat.fromBitsLE (count c)
  let K := fun c => Nat.fromBitsLE (index c)
  let L := fun c => K c * (N c + 1) + N c
  let p := Classical.choose (Cobham.output_length_poly_of_mem_FP (limit_mem_FP hc hi))
  have hp : ∀ c, (limit count index c).length ≤ p.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP (limit_mem_FP hc hi))
  have hdFP := mem_FP_comp (mem_FP_pair hc hc) BinaryNat.add_mem_FP
  let d := Classical.choose (Cobham.output_length_poly_of_mem_FP hdFP)
  have hd : ∀ c, ((BinaryNat.add ∘ fun x => pair (count x) (count x)) c).length ≤ d.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hdFP)
  let r := 2 * Polynomial.X + 2 * p + d + 4
  let q := 2 * Polynomial.X + 3 * p + 4
  let P := program E count
  let T := childTime E count
  let F := SubroutineIteration.abstractStep P T
  have hL (c : List Bool) : (L c).size ≤ p.eval c.length := by
    have h := hp c
    rw [limit_code, BinaryNatCode.length_encode] at h
    exact h
  have hN (c : List Bool) : N c ≤ L c := by dsimp only [L]; omega
  have hdN (c : List Bool) : (2 * N c).size ≤ d.eval c.length := by
    simpa only [Function.comp_apply, BinaryNat.add_eq_bits, pairFst_pair, pairSnd_pair,
      Nat.size_eq_bits_len, two_mul, N] using hd c
  have hquery (c : List Bool) (t : ℕ) (ht : t ≤ L c) : (query count (F^[t] (init c))).length ≤ q.eval c.length := by
    rw [iterate_packet E count c (N c) (a c) rfl (hbits c), query_packet count c (N c) t _ rfl]
    simp only [pair_length, BinaryNatCode.length_encode]
    have hpos : t % (N c + 1) ≤ L c := by
      have := Nat.mod_lt t (by omega : 0 < N c + 1)
      have := hN c
      omega
    have hs1 := (Nat.size_le_size hpos).trans (hL c)
    have hs2 := (Nat.size_le_size ((Nat.div_le_self t (N c + 1)).trans ht)).trans (hL c)
    simp only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    omega
  have E' : SpaceFunction (fun c => output (F^[L c] (init c))) := by
    refine SubroutineIteration.evaluator P (program_polyTime E hc) init init_mem_FP
      (halted count index) output (halted_mem_FP hc hi) output_mem_FP T L r (E.space.comp q)
      p (E.clock.comp q) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro c t _ _
      exact ⟨E.before (query count (F^[t] (init c))), E.after (query count (F^[t] (init c)))⟩
    · intro c t ht
      rw [iterate_packet E count c (N c) (a c) rfl (hbits c)]
      simp only [packet, pair_length, BinaryNatCode.length_encode]
      have hs := (Nat.size_le_size ht).trans (hL c)
      have hv := (Nat.size_le_size (BinarySum.carryValue_le (N c) (a c) t)).trans (hdN c)
      simp only [r, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
      omega
    · intro c t ht _ j hj
      have hl := E.length_le (query count (F^[t] (init c))) j hj
      have hm := polynomial_eval_mono_nat E.space (hquery c t ht.le)
      simpa only [P, program, F, T, childTime, Function.comp_apply, Polynomial.eval_comp] using hl.trans hm
    · intro c
      exact (Nat.lt_size_self (L c)).le.trans (Nat.pow_le_pow_right (by decide) (hL c))
    · intro c t ht _
      have hl := E.time_le (query count (F^[t] (init c)))
      have hm := polynomial_eval_mono_nat E.clock (hquery c t ht.le)
      simpa only [F, T, childTime, Polynomial.eval_comp] using
        hl.trans (Nat.pow_le_pow_right (by decide) hm)
    · intro c t ht
      rw [iterate_packet E count c (N c) (a c) rfl (hbits c), halted_packet]
      exact decide_eq_false (Nat.not_le_of_lt ht)
    · intro c
      rw [iterate_packet E count c (N c) (a c) rfl (hbits c), halted_packet]
      exact decide_eq_true (le_refl (L c))
  exact E'.congr (funext fun c => output_end E count c (N c) (K c) (a c) rfl (hbits c))

end LeanCanny.Computation.SumBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedScan

/-!
# Polynomial-space bounded universal scans

An FP binary bound permits exponentially many sequential calls to a certified
space decider. The saved parent and child states, and the expanded physical
clock, satisfy the suspended-iteration contracts.
-/

@[expose] public section

namespace LeanCanny.Computation.BoundedScan
open Complexity
open LeanCanny.Encoding

def language (L : Language) (N : List Bool → ℕ) : Language :=
  {c | ∀ k < N c, pair c (BinaryNatCode.encode k) ∈ L}

noncomputable def decider {L : Language} (D : SpaceDecider L)
    (bound : List Bool → List Bool) (hb : bound ∈ FP) (N : List Bool → ℕ)
    (hbound : ∀ c, bound c = BinaryNatCode.encode (N c)) : SpaceDecider (language L N) := by
  let pd := Classical.choose (Cobham.output_length_poly_of_mem_FP hb)
  have hd : ∀ c, (bound c).length ≤ pd.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hb)
  have hs := mem_FP_comp hb BinaryNat.succ_mem_FP
  let ps := Classical.choose (Cobham.output_length_poly_of_mem_FP hs)
  have hsp : ∀ c, ((BinaryNat.succ ∘ bound) c).length ≤ ps.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hs)
  let p := pd + ps
  let r := 2 * Polynomial.X + 2 * p + 5
  let q := 2 * Polynomial.X + p + 2
  let P := program D bound
  let T := childTime D
  let f := SubroutineIteration.abstractStep P T
  have hbits (c : List Bool) : (N c).size + (N c + 1).size ≤ p.eval c.length := by
    have hdc := hd c
    have hsc := hsp c
    rw [hbound, BinaryNatCode.length_encode] at hdc
    simp only [Function.comp_apply, hbound, BinaryNat.succ_eq_bits,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.size_eq_bits_len] at hsc
    simp only [p, Polynomial.eval_add]
    omega
  have hquery (c : List Bool) (j : ℕ) (hj : j ≤ N c) :
      (query (f^[j] (init c))).length ≤ q.eval c.length := by
    rw [iterate_packet D bound c (N c) j (hbound c) hj, query_packet, pair_length,
      BinaryNatCode.length_encode]
    have hsize := Nat.size_le_size hj
    have hc := hbits c
    simp only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    omega
  refine SubroutineIteration.decider P (program_polyTime D hb) init init_mem_FP
    (halted bound) accumulator (halted_mem_FP hb) accumulator_mem_FP T N r (D.space.comp q)
    p (D.clock.comp q) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro c j _ _
    exact ⟨D.before (query (f^[j] (init c))), D.after (query (f^[j] (init c)))⟩
  · intro c j hj
    rw [iterate_packet D bound c (N c) j (hbound c) hj]
    simp only [packet, pair_length, List.length_singleton, BinaryNatCode.length_encode]
    have hsize := Nat.size_le_size (show j + 1 ≤ N c + 1 by omega)
    have hc := hbits c
    simp only [r, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    omega
  · intro c j hj _ v hv
    have hl := D.length_le (query (f^[j] (init c))) v hv
    have hm := polynomial_eval_mono_nat D.space (hquery c j (by omega))
    simpa only [P, program, f, T, childTime, Polynomial.eval_comp] using hl.trans hm
  · intro c
    have hc := hbits c
    exact (Nat.lt_size_self (N c)).le.trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  · intro c j hj _
    have ht := D.time_le (query (f^[j] (init c)))
    have hm := polynomial_eval_mono_nat D.clock (hquery c j (by omega))
    simpa only [f, T, childTime, Polynomial.eval_comp] using
      ht.trans (Nat.pow_le_pow_right (by decide) hm)
  · intro c j hj
    rw [iterate_packet D bound c (N c) j (hbound c) hj.le,
      halted_packet bound c (N c) j _ (hbound c)]
    simp only [decide_eq_false_iff_not]
    omega
  · intro c
    rw [iterate_packet D bound c (N c) (N c) (hbound c) le_rfl,
      halted_packet bound c (N c) (N c) _ (hbound c)]
    simp
  · intro c
    rw [iterate_packet D bound c (N c) (N c) (hbound c) le_rfl, accumulator_packet]
    exact (allBelow_correct D c (N c)).symm

theorem language_mem_PSPACE {L : Language} (D : SpaceDecider L)
    (bound : List Bool → List Bool) (hb : bound ∈ FP) (N : List Bool → ℕ)
    (hbound : ∀ c, bound c = BinaryNatCode.encode (N c)) : language L N ∈ PSPACE :=
  (decider D bound hb N hbound).mem_PSPACE

end LeanCanny.Computation.BoundedScan

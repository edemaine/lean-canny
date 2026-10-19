/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedProductSubroutine
public import LeanCanny.Algebra.BalancedProductPadding
public import LeanCanny.Computation.SpaceFunctionComposition

/-!
# A uniform space-bounded evaluator for balanced product bits

The factor count may be exponential in its binary word length. Only the count
and selected-index writers are FP; individual factor bits come from a certified
space-bounded routine. The complete physical run includes every suspended leaf
state and the expanded call clock. No product or factor is materialized.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedProduct
open Complexity
open LeanCanny.Computation
open Controller

def treeValue (count index : List Bool → List Bool) (a : List Bool → ℕ → ℕ) (c : List Bool) : List Bool :=
  if (tree (a c) (count c).length 0).testBit (Nat.fromBitsLE (index c)) then [true] else []

noncomputable def treeEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count index : List Bool → List Bool) (hc : count ∈ FP) (hi : index ∈ FP)
    (a : List Bool → ℕ → ℕ)
    (hbits : ∀ c i k, (f (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false =
      (a c i).testBit k) : SpaceFunction (treeValue count index a) := by
  let H := fun c => (count c).length
  let K := fun c => Nat.fromBitsLE (index c)
  let N := fun c => time (a c) (H c) (K c)
  let init := initialPacket count index
  let P := Suspended.program E
  let T := Suspended.childTime E
  let F := SubroutineIteration.abstractStep P T
  let pc := Classical.choose (Cobham.output_length_poly_of_mem_FP hc)
  have hpc : ∀ c, H c ≤ pc.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hc)
  let pi := Classical.choose (Cobham.output_length_poly_of_mem_FP hi)
  have hpi : ∀ c, (index c).length ≤ pi.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hi)
  have hK (c : List Bool) : (K c).size ≤ pi.eval c.length :=
    (Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length (index c))).trans (hpi c)
  let r := 2 * Polynomial.X + 2 + 128 * (pc + pi + 1) ^ 2
  let w := pc * (2 * pi + 5) + 1
  let pq := Classical.choose (Cobham.output_length_poly_of_mem_FP leafQuery_mem_FP)
  have hpq : ∀ p, (leafQuery p).length ≤ pq.eval p.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP leafQuery_mem_FP)
  let q := pq.comp r
  have hiter (c : List Bool) (t : ℕ) :
      F^[t] (init c) = pair c (stateBits ((step (a c))^[t] (start (H c) (K c)))) := by
    dsimp only [F, P, T, init, H, K]
    rw [initialPacket_encode, Suspended.iterate_packet E c (a c) (hbits c)]
  have hp (c : List Bool) (t : ℕ) : (F^[t] (init c)).length ≤ r.eval c.length := by
    rw [hiter, pair_length]
    have hb := run_stateBits_length_le (a c) (H c) (K c) t
    have hsum : H c + (K c).size + 1 ≤ pc.eval c.length + pi.eval c.length + 1 := by
      have := hpc c; have := hK c; omega
    have hpow := Nat.pow_le_pow_left hsum 2
    simp only [r, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    omega
  have hquery (c : List Bool) (t : ℕ) : (leafQuery (F^[t] (init c))).length ≤ q.eval c.length := by
    simpa only [q, Polynomial.eval_comp] using
      (hpq (F^[t] (init c))).trans (polynomial_eval_mono_nat pq (hp c t))
  have E' : SpaceFunction (fun c => Suspended.output (F^[N c] (init c))) := by
    refine SubroutineIteration.evaluator P (Suspended.program_polyTime E) init (initialPacket_mem_FP hc hi)
      Suspended.halted Suspended.output Suspended.halted_mem_FP Suspended.output_mem_FP
      T N r (E.space.comp q) w (E.clock.comp q) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro c t _ _
      exact Suspended.child_terminates E (F^[t] (init c))
    · intro c t _
      exact hp c t
    · intro c t _ _ j hj
      have hl := E.length_le (leafQuery (F^[t] (init c))) j hj
      have hm := polynomial_eval_mono_nat E.space (hquery c t)
      simpa only [F, P, Suspended.program, T, Suspended.childTime, Function.comp_apply, Polynomial.eval_comp]
        using hl.trans hm
    · intro c
      have he : H c * (2 * (K c).size + 5) + 1 ≤ w.eval c.length := by
        have hm := Nat.mul_le_mul (hpc c) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hK c)) 5)
        simpa only [w, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one] using
          Nat.add_le_add_right hm 1
      exact (time_exp_bound (a c) (H c) (K c)).trans (Nat.pow_le_pow_right (by decide) he)
    · intro c t _ _
      have hl := E.time_le (leafQuery (F^[t] (init c)))
      have hm := polynomial_eval_mono_nat E.clock (hquery c t)
      simpa only [T, Suspended.childTime, Polynomial.eval_comp] using
        hl.trans (Nat.pow_le_pow_right (by decide) hm)
    · intro c t ht
      rw [hiter, Suspended.halted_packet]
      exact before (a c) (H c) (K c) t ht
    · intro c
      rw [hiter, Suspended.halted_packet]
      exact after (a c) (H c) (K c)
  refine E'.congr (funext fun c => ?_)
  rw [hiter]
  obtain ⟨b, he, hb⟩ := result (a c) (H c) (K c)
  rw [he, Suspended.output_done, hb]
  rfl

end LeanCanny.Algebra.BalancedProduct

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedProductStepSpace
public import LeanCanny.Algebra.BalancedProductPadding
public import LeanCanny.Computation.SpaceIteration

/-! # A native space certificate for balanced product bits

FP count/index writers and a tidy space-bounded factor-bit reader suffice.
Continuation invariants bound the semantic controller's encoded states and
abstract stopping index. Native iteration hides all child execution times. -/

@[expose] public section

namespace LeanCanny.Algebra.BalancedProduct

open LeanCanny.Computation
open Controller

def treeValue (count index : List Bool → List Bool) (a : List Bool → ℕ → ℕ) (c : List Bool) : List Bool :=
  if (tree (a c) (count c).length 0).testBit (Nat.fromBitsLE (index c)) then [true] else []

theorem treeEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count index : List Bool → List Bool) (hc : count ∈ FP) (hi : index ∈ FP)
    (a : List Bool → ℕ → ℕ)
    (hbits : ∀ c i k, (f (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false =
      (a c i).testBit k) : SpaceFunction (treeValue count index a) := by
  let H := fun c => (count c).length
  let K := fun c => Nat.fromBitsLE (index c)
  let N := fun c => time (a c) (H c) (K c)
  let init := initialPacket count index
  let F := Controller.step f
  let pc := Classical.choose (output_length_poly_of_mem_FP hc)
  have hpc : ∀ c, H c ≤ pc.eval c.length :=
    Classical.choose_spec (output_length_poly_of_mem_FP hc)
  let pi := Classical.choose (output_length_poly_of_mem_FP hi)
  have hpi : ∀ c, (index c).length ≤ pi.eval c.length :=
    Classical.choose_spec (output_length_poly_of_mem_FP hi)
  have hK (c : List Bool) : (K c).size ≤ pi.eval c.length :=
    (Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length (index c))).trans (hpi c)
  let r := 2 * Polynomial.X + 2 + 128 * (pc + pi + 1) ^ 2
  let w := pc * (2 * pi + 5) + 1
  have hiter (c : List Bool) (t : ℕ) :
      F^[t] (init c) = pair c (stateBits ((step (a c))^[t] (start (H c) (K c)))) := by
    dsimp only [F, init, H, K]
    rw [initialPacket_encode, Controller.iterate_packet f c (a c) (hbits c)]
  have hp (c : List Bool) (t : ℕ) : (F^[t] (init c)).length ≤ r.eval c.length := by
    rw [hiter, pair_length]
    have hb := run_stateBits_length_le (a c) (H c) (K c) t
    have hsum : H c + (K c).size + 1 ≤ pc.eval c.length + pi.eval c.length + 1 := by
      have := hpc c; have := hK c; omega
    have hpow := Nat.pow_le_pow_left hsum 2
    simp only [r, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    omega
  have E' : SpaceFunction (fun c => SpaceStep.output (F^[N c] (init c))) := by
    refine SpaceFunction.orbit (SpaceStep.stepEvaluator E) init (initialPacket_mem_FP hc hi)
      SpaceStep.halted SpaceStep.output SpaceStep.halted_mem_FP SpaceStep.output_mem_FP
      N r w (fun c t _ => hp c t) ?_ ?_ ?_
    · intro c
      have he : H c * (2 * (K c).size + 5) + 1 ≤ w.eval c.length := by
        have hm := Nat.mul_le_mul (hpc c) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hK c)) 5)
        simpa only [w, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one] using
          Nat.add_le_add_right hm 1
      exact (time_exp_bound (a c) (H c) (K c)).trans (Nat.pow_le_pow_right (by decide) he)
    · intro c t ht
      rw [hiter, SpaceStep.halted_packet]
      exact before (a c) (H c) (K c) t ht
    · intro c
      rw [hiter, SpaceStep.halted_packet]
      exact after (a c) (H c) (K c)
  refine E'.congr (funext fun c => ?_)
  rw [hiter]
  obtain ⟨b, he, hb⟩ := result (a c) (H c) (K c)
  rw [he, SpaceStep.output_done, hb]
  rfl

end LeanCanny.Algebra.BalancedProduct

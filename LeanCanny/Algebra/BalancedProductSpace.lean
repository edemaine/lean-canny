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
  let r := fun c => 2 * c.length + 2 + 128 * (H c + (K c).size + 1) ^ 2
  let w := fun c => H c * (2 * (K c).size + 5) + 1
  have hH : Turing.MultiTapeTM.PolyBounded List.length H := hc.polyBounded_length
  have hK : Turing.MultiTapeTM.PolyBounded List.length (fun c => (K c).size) :=
    hi.polyBounded_length.mono (fun c => Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length (index c)))
  have hr : Turing.MultiTapeTM.PolyBounded List.length r := by
    simpa only [r, pow_two] using
      (((Turing.MultiTapeTM.PolyBounded.const 2).mul Turing.MultiTapeTM.PolyBounded.self).add (.const 2)).add
        ((Turing.MultiTapeTM.PolyBounded.const 128).mul
          (((hH.add hK).add (.const 1)).mul ((hH.add hK).add (.const 1))))
  have hw : Turing.MultiTapeTM.PolyBounded List.length w :=
    (hH.mul (((Turing.MultiTapeTM.PolyBounded.const 2).mul hK).add (.const 5))).add (.const 1)
  have hiter (c : List Bool) (t : ℕ) :
      F^[t] (init c) = pair c (stateBits ((step (a c))^[t] (start (H c) (K c)))) := by
    dsimp only [F, init, H, K]
    rw [initialPacket_encode, Controller.iterate_packet f c (a c) (hbits c)]
  have hp (c : List Bool) (t : ℕ) : (F^[t] (init c)).length ≤ r c := by
    rw [hiter, pair_length]
    have hb := run_stateBits_length_le (a c) (H c) (K c) t
    dsimp only [r]
    omega
  have E' : SpaceFunction (fun c => SpaceStep.output (F^[N c] (init c))) := by
    refine SpaceFunction.orbit_of_polyBounded (SpaceStep.stepEvaluator E) init (initialPacket_mem_FP hc hi)
      SpaceStep.halted SpaceStep.output SpaceStep.halted_mem_FP SpaceStep.output_mem_FP
      N r w hr hw (fun c t _ => hp c t) (fun c => time_exp_bound (a c) (H c) (K c)) ?_ ?_
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

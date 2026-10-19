/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFold
public import LeanCanny.Computation.SpaceFunctionComposition

/-!
# Space and clock accounting for bounded folds

The accumulator-length contract concerns the mathematical fold prefixes.
The resulting certificate accounts for the saved context/counter/accumulator
and all update-subroutine states, with an exponential bound on the full clock.
-/

@[expose] public section

namespace LeanCanny.Computation.BoundedFold
open Complexity
open LeanCanny.Encoding

noncomputable def evaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (bound seed : List Bool → List Bool) (hb : bound ∈ FP) (hs : seed ∈ FP)
    (s : Polynomial ℕ)
    (hstate : ∀ c i, i ≤ Nat.fromBitsLE (bound c) → (fold f seed c i).length ≤ s.eval c.length) :
    SpaceFunction (fun c => fold f seed c (Nat.fromBitsLE (bound c))) := by
  let p := Classical.choose (Cobham.output_length_poly_of_mem_FP hb)
  have hp : ∀ c, (bound c).length ≤ p.eval c.length := Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hb)
  let N := fun c => Nat.fromBitsLE (bound c)
  let r := 2 * Polynomial.X + 2 * p + s + 4
  let P := program E
  let F := SubroutineIteration.abstractStep P E.time
  have hbits (c : List Bool) : (N c).size ≤ p.eval c.length :=
    (Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length (bound c))).trans (hp c)
  have hparent (c : List Bool) (i : ℕ) (hi : i ≤ N c) : (F^[i] (init seed c)).length ≤ r.eval c.length := by
    rw [iterate_packet E seed c i]
    simp only [packet, pair_length, BinaryNatCode.length_encode]
    have ht := (Nat.size_le_size hi).trans (hbits c)
    have hv := hstate c i hi
    simp only [r, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    omega
  have E' := SubroutineIteration.evaluator P (program_polyTime E) (init seed) (init_mem_FP hs)
    (halted bound) accumulator (halted_mem_FP hb) accumulator_mem_FP E.time N r (E.space.comp r)
    p (E.clock.comp r)
    (by intro c i _ _; exact ⟨E.before (F^[i] (init seed c)), E.after (F^[i] (init seed c))⟩)
    hparent
    (by
      intro c i hi _ j hj
      have hl := E.length_le (F^[i] (init seed c)) j hj
      have hm := polynomial_eval_mono_nat E.space (hparent c i hi.le)
      simpa only [F, P, program, Polynomial.eval_comp] using hl.trans hm)
    (by intro c; exact (Nat.lt_size_self (N c)).le.trans (Nat.pow_le_pow_right (by decide) (hbits c)))
    (by
      intro c i hi _
      have hl := E.time_le (F^[i] (init seed c))
      have hm := polynomial_eval_mono_nat E.clock (hparent c i hi.le)
      simpa only [Polynomial.eval_comp] using hl.trans (Nat.pow_le_pow_right (by decide) hm))
    (by
      intro c i hi
      rw [iterate_packet E seed c i, halted_packet]
      exact decide_eq_false (Nat.not_le_of_lt hi))
    (by
      intro c
      rw [iterate_packet E seed c (N c), halted_packet]
      exact decide_eq_true (le_refl (N c)))
  refine E'.congr (funext fun c => ?_)
  rw [iterate_packet E seed c (N c), accumulator_packet]

end LeanCanny.Computation.BoundedFold

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Factorial

/-! # Uniform falling factorial residues for binary derivative orders -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

@[expose] noncomputable def fallingFactorialResidue (p i k : ℕ) : ℕ :=
  if k ≤ i then
    (factorialResidue p i * powMod p (factorialResidue p (i - k)) (p - 2)) % p
  else 0

/-- Both factorials share one fixed counting-level certificate. -/
theorem fallingFactorialResidue_mem {α : Type} {enc : α ↪ List Bool}
    {p i k : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hi : ComputableInPolyTime i enc encNat)
    (hk : ComputableInPolyTime k enc encNat) :
    (fun w => fallingFactorialResidue (p w) (i w) (k w)) ∈
      CountingFunction 3 enc encNat := by
  have hnum := CountingFunction.preprocess factorialResidue_mem (hp.prod hi)
  have hden := CountingFunction.preprocess factorialResidue_mem
    (hp.prod (ComputableInPolyTime.binary_sub' hi hk))
  have hinv := CountingFunction.powMod (CountingFunction.of_polyTime hp) hden
    (CountingFunction.of_polyTime (ComputableInPolyTime.binary_sub' hp (.const 2)))
  have hval := CountingFunction.nat_mod (CountingFunction.nat_mul hnum hinv)
    (CountingFunction.of_polyTime hp)
  have htest : ComputableInPolyTime (fun w => decide (k w ≤ i w)) enc encBool := by
    fun_prop
  simpa only [fallingFactorialResidue, decide_eq_true_eq] using
    CountingFunction.ite (CountingFunction.of_polyTime htest) hval
      (CountingFunction.of_polyTime (ComputableInPolyTime.const 0))

/-- The same total evaluator handles orders above the monomial degree. -/
theorem fallingFactorialResidue_cast {p i k : ℕ} [Fact p.Prime] (hi : i < p) :
    (fallingFactorialResidue p i k : ZMod p) = (i.descFactorial k : ZMod p) := by
  by_cases hk : k ≤ i
  · rw [fallingFactorialResidue, ite_eq_left hk, ZMod.natCast_mod, Nat.cast_mul,
      factorialResidue_cast, factorialResidue_inverse ((Nat.sub_le i k).trans_lt hi)]
    have hfac : ((i - k).factorial : ZMod p) ≠ 0 := by
      rw [← factorialResidue_cast]
      exact factorialResidue_ne_zero ((Nat.sub_le i k).trans_lt hi)
    have heq := congrArg (fun n : ℕ => (n : ZMod p)) (Nat.factorial_mul_descFactorial hk)
    simp only [Nat.cast_mul] at heq
    rw [← heq]
    field_simp
  · simp only [fallingFactorialResidue, ite_eq_right hk,
      Nat.descFactorial_of_lt (Nat.lt_of_not_ge hk), Nat.cast_zero]

end LeanCanny.CountingHierarchy

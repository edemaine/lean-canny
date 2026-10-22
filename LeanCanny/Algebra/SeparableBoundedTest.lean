/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ResultantBoundedTest
public import LeanCanny.Algebra.SeparableSpace

/-! # A total separability test for partially prepared contexts

Original coefficient access and supplied binary degree/height controls give
a native space test on every input. Correctness needs nonzeroness, the exact
degree, and a height bound only at the tested context. This supports a table
preparation invariant without requiring every possible table to be consistent.
-/

@[expose] public section

namespace LeanCanny.Algebra.SeparableBoundedTest
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open Turing.MultiTapeTM
open scoped Classical

def derivativeCoefficient (coefficient : List Bool → List Bool) : List Bool → List Bool :=
  DerivativeBits.value SeparableBits.modulus coefficient

theorem derivative_packet (p : List Bool → ℤ[X]) (coefficient : List Bool → List Bool)
    (hc : ∀ c k, coefficient (pair c (BinaryNatCode.encode k)) =
      residueBits (((p (pairFst c)).coeff k : ℤ) : ZMod (Nat.fromBitsLE (pairSnd c) + 1)))
    (c : List Bool) (k : ℕ) :
    derivativeCoefficient coefficient (pair c (BinaryNatCode.encode k)) =
      residueBits ((((p (pairFst c)).derivative).coeff k : ℤ) : ZMod (Nat.fromBitsLE (pairSnd c) + 1)) := by
  have h := DerivativeBits.packet SeparableBits.modulus coefficient c _
    ((p (pairFst c)).map (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd c) + 1))))
    (by simp only [SeparableBits.modulus, BinaryNat.succ_eq_bits, BinaryNatCode.encode])
    (fun j => by simpa only [coeff_map, Int.coe_castRingHom] using hc c j) k
  simpa only [derivativeCoefficient, derivative_map, coeff_map, Int.coe_castRingHom] using h

def budget (degree height : List Bool → ℕ) (c : List Bool) : ℕ :=
  (degree c + (degree c - 1)).size * (degree c + (degree c - 1)) +
    (degree c + (degree c - 1)) * (height c + (degree c).size) + 1

theorem budget_binary {degree height : List Bool → ℕ} (hd : BinaryFn degree) (hb : BinaryFn height) :
    BinaryFn (budget degree height) := by
  have hn : BinaryFn (fun c => degree c - 1) := ComputableTidilyInPolyTime.binary_sub' hd (BinaryFn.const 1)
  have hdim := hd.add hn
  exact ((hdim.size.mul hdim).add (hdim.mul (hb.add hd.size))).add (BinaryFn.const 1)

def language (p : List Bool → ℤ[X]) (degree height : List Bool → ℕ) : Language :=
  {c | c ∉ ResultantBoundedTest.language p (fun c => (p c).derivative)
    degree (fun c => degree c - 1) (budget degree height)}

theorem decider (p : List Bool → ℤ[X]) (coefficient : List Bool → List Bool)
    (hc : ∀ c k, coefficient (pair c (BinaryNatCode.encode k)) =
      residueBits (((p (pairFst c)).coeff k : ℤ) : ZMod (Nat.fromBitsLE (pairSnd c) + 1)))
    (E : SpaceFunction coefficient) (degree height : List Bool → ℕ) (hd : BinaryFn degree) (hb : BinaryFn height) :
    SpaceDecider (language p degree height) := by
  have hn : BinaryFn (fun c => degree c - 1) := ComputableTidilyInPolyTime.binary_sub' hd (BinaryFn.const 1)
  have ER := DerivativeBits.evaluator E SeparableBits.modulus SeparableBits.modulus_FP
  have D := ResultantBoundedTest.decider p (fun c => (p c).derivative) degree (fun c => degree c - 1)
    coefficient (derivativeCoefficient coefficient) hc (derivative_packet p coefficient hc) hd hn E ER
    (budget degree height) (budget_binary hd hb)
  refine D.flagEvaluator.decider (fun b => !(b[0]?.getD false)) ?_ ?_
  · simpa using (FPPred.getBit id_mem_FP (UnaryFn.const 0)).not.flag_mem_FP
  · intro c
    simp only [language, Set.mem_ofPred_eq, List.getElem?_cons_zero, Option.getD_some,
      Bool.not_eq_true', decide_eq_false_iff_not]

theorem budget_correct_at (p : List Bool → ℤ[X]) (degree height : List Bool → ℕ) (c : List Bool)
    (hd : (p c).natDegree = degree c) (hb : ∀ k, ((p c).coeff k).natAbs ≤ 2 ^ height c) :
    ((p c).resultant (p c).derivative (degree c) (degree c - 1)).natAbs.size ≤ budget degree height c := by
  apply SylvesterBits.resultant_size_le
  · intro k
    exact (hb k).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  · intro k
    simpa only [hd] using SeparableBits.derivative_bound (p c) (height c) hb k

/-- Nonzero constants are included. No promise is made about the test's
separability interpretation at contexts with invalid degree/height metadata. -/
theorem correct_at (p : List Bool → ℤ[X]) (degree height : List Bool → ℕ) (c : List Bool)
    (hp : p c ≠ 0) (hd : (p c).natDegree = degree c) (hb : ∀ k, ((p c).coeff k).natAbs ≤ 2 ^ height c) :
    c ∈ language p degree height ↔ ((p c).map (Int.castRingHom ℚ)).Separable := by
  change (c ∉ ResultantBoundedTest.language p (fun c => (p c).derivative)
    degree (fun c => degree c - 1) (budget degree height)) ↔ _
  rw [ResultantBoundedTest.correct_at p (fun c => (p c).derivative) degree (fun c => degree c - 1)
    (budget degree height) c (budget_correct_at p degree height c hd hb)]
  rw [← hd, ← natDegree_derivative]
  exact (integer_separable_iff_resultant_ne_zero (p c) hp).symm

end LeanCanny.Algebra.SeparableBoundedTest

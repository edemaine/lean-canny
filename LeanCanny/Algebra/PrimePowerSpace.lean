/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFoldSpace
public import LeanCanny.Computation.SpaceFunctionBranch
public import LeanCanny.Encoding.BinaryMulFP
public import Mathlib.Data.Nat.Log

/-!
# Maximal powers below a binary bound

Starting at one, multiply by the base while the candidate remains below the
bound. After `N+1` updates the result is `p^(log p N)`, including bases zero
and one and bound zero. Every intermediate magnitude is at most `N+1`.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrimePowerBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation

def growth (N p : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => if 2 ≤ p ∧ growth N p i * p ≤ N then growth N p i * p else growth N p i

theorem growth_le (N p i : ℕ) : growth N p i ≤ N + 1 := by
  induction i with
  | zero => simp [growth]
  | succ i ih =>
    rw [growth]
    split_ifs with h
    · omega
    · exact ih

theorem growth_zero (p i : ℕ) : growth 0 p i = 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [growth, ih]
    split_ifs with h
    · simp only [one_mul] at h
      omega
    · rfl

theorem growth_eq (N p i : ℕ) : growth N p i = p ^ min i (p.log N) := by
  by_cases hN : N = 0
  · subst N
    simp only [growth_zero, Nat.log_zero_right, Nat.min_zero, pow_zero]
  by_cases hp : 2 ≤ p
  · induction i with
    | zero => simp [growth]
    | succ i ih =>
      rw [growth, ih]
      have hcond : p ^ min i (p.log N) * p ≤ N ↔ i < p.log N := by
        rw [← pow_succ, ← Nat.le_log_iff_pow_le (by omega : 1 < p) hN]
        omega
      by_cases hi : i < p.log N
      · rw [ite_eq_left ⟨hp, hcond.mpr hi⟩, Nat.min_eq_left hi.le,
          Nat.min_eq_left (by omega : i + 1 ≤ p.log N), pow_succ]
      · rw [ite_eq_right (by rintro ⟨_, h⟩; exact hi (hcond.mp h)),
          Nat.min_eq_right (by omega : p.log N ≤ i), Nat.min_eq_right (by omega : p.log N ≤ i + 1)]
  · have hlog := Nat.log_of_left_le_one (by omega : p ≤ 1) N
    induction i with
    | zero => simp [growth]
    | succ i ih => simp only [growth, ih, hp, false_and, ↓reduceIte, hlog, Nat.min_zero, pow_zero]

def candidate (q : List Bool) : List Bool :=
  BinaryNat.mul (pair (BoundedFold.accumulator q) (pairSnd (pairFst q)))

def allowed (q : List Bool) : Prop :=
  2 ≤ Nat.fromBitsLE (pairSnd (pairFst q)) ∧ Nat.fromBitsLE (candidate q) ≤ Nat.fromBitsLE (pairFst (pairFst q))

instance (q : List Bool) : Decidable (allowed q) := inferInstanceAs (Decidable (_ ∧ _))

def update (q : List Bool) : List Bool := if allowed q then candidate q else BinaryNat.normalize (BoundedFold.accumulator q)

theorem candidate_mem_FP : candidate ∈ FP := by
  have hb := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have h := mem_FP_comp (mem_FP_pair BoundedFold.accumulator_mem_FP hb) BinaryNat.mul_mem_FP
  refine mem_FP_of_eq (g := candidate) h ?_
  intro q
  simp only [Function.comp_apply, candidate]

theorem allowed_fppred : FPPred allowed :=
  (BinaryNat.le_fppred (constFn_mem_FP [false, true]) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)).and
    (BinaryNat.le_fppred candidate_mem_FP (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))

theorem update_mem_FP : update ∈ FP :=
  allowed_fppred.ite_mem_FP candidate_mem_FP (mem_FP_comp BoundedFold.accumulator_mem_FP BinaryNat.normalize_mem_FP)

theorem fold_eq (c : List Bool) (i : ℕ) :
    BoundedFold.fold update (fun _ => [true]) c i =
      (growth (Nat.fromBitsLE (pairFst c)) (Nat.fromBitsLE (pairSnd c)) i).bits := by
  induction i with
  | zero => simp [BoundedFold.fold, growth]
  | succ i ih =>
    rw [BoundedFold.fold, ih]
    simp only [update, allowed, candidate, BoundedFold.accumulator_packet, BoundedFold.context_packet,
      BinaryNat.mul_pair, Nat.fromBitsLE_bits, BinaryNat.normalize_eq_bits, growth]
    split_ifs <;> rfl

theorem evaluator : SpaceFunction (fun c =>
    (Nat.fromBitsLE (pairSnd c) ^ (Nat.fromBitsLE (pairSnd c)).log (Nat.fromBitsLE (pairFst c))).bits) := by
  have hb := mem_FP_comp pairFst_mem_FP BinaryNat.succ_mem_FP
  have hs : ∀ c i, i ≤ Nat.fromBitsLE ((BinaryNat.succ ∘ pairFst) c) →
      (BoundedFold.fold update (fun _ => [true]) c i).length ≤ (Polynomial.X + 1 : Polynomial ℕ).eval c.length := by
    intro c i _
    rw [fold_eq, Nat.size_eq_bits_len]
    have hraw := (Nat.fromBitsLE_lt_pow_length (pairFst c)).trans_le
      (Nat.pow_le_pow_right (by decide) (pairFst_length_le c))
    have hpow : Nat.fromBitsLE (pairFst c) + 1 < 2 ^ (c.length + 1) := by
      rw [pow_succ]
      have := pow_pos (by decide : 0 < (2 : ℕ)) c.length
      omega
    have h := Nat.size_le.mpr ((growth_le (Nat.fromBitsLE (pairFst c)) (Nat.fromBitsLE (pairSnd c)) i).trans_lt hpow)
    simpa only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using h
  let E := BoundedFold.evaluator (SpaceFunction.ofFP update update_mem_FP) (BinaryNat.succ ∘ pairFst)
    (fun _ => [true]) hb (constFn_mem_FP [true]) (Polynomial.X + 1) hs
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, fold_eq, growth_eq]
  rw [Nat.min_eq_right (Nat.le_succ_of_le (Nat.log_le_self _ _))]

end LeanCanny.Algebra.PrimePowerBits

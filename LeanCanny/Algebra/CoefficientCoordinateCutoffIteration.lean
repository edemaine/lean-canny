/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientCoordinateDyadicBounds

/-! # One original budget for unary-many actual normalization cutoffs -/

@[expose] public section
namespace LeanCanny.Algebra.CoefficientCoordinateDyadicBounds

def cutoffStep (rank K H C : ℕ) : ℕ := max C (cutBudget rank C K H)

def cutoffGrowth (rank K H : ℕ) : ℕ := 2 * rank * K + cutBudget rank 0 K H + 1

def stageBudget (rank K H initial stage : ℕ) : ℕ := cutoffGrowth rank K H ^ stage * (initial + 1)

def cutoffIteration (rank K H initial : ℕ) : ℕ → ℕ
  | 0 => initial
  | stage + 1 => cutoffStep rank K H (cutoffIteration rank K H initial stage)

theorem cutBudget_mono {rank rank' C C' K K' H H' : ℕ}
    (hr : rank ≤ rank') (hc : C ≤ C') (hk : K ≤ K') (hh : H ≤ H') :
    cutBudget rank C K H ≤ cutBudget rank' C' K' H' := by
  have HM : IntegerPolynomialDyadic.massBudget C K H ≤ IntegerPolynomialDyadic.massBudget C' K' H' := by
    unfold IntegerPolynomialDyadic.massBudget
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add hh (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hk) (Nat.add_le_add hc hk))) hk)
      (Nat.mul_le_mul_left 2 (Nat.size_le_size (Nat.add_le_add_right hk 1)))
  unfold cutBudget ParameterMatrixMassBounds.characteristicBudget
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul (Nat.size_le_size hr) hr)
      (Nat.mul_le_mul hr (Nat.add_le_add_right HM 1))) 1

theorem cutoffStep_mono {rank rank' K K' H H' C C' : ℕ}
    (hr : rank ≤ rank') (hk : K ≤ K') (hh : H ≤ H') (hc : C ≤ C') :
    cutoffStep rank K H C ≤ cutoffStep rank' K' H' C' :=
  max_le_max hc (cutBudget_mono hr hc hk hh)

theorem cutoffGrowth_positive (rank K H : ℕ) : 1 ≤ cutoffGrowth rank K H := by
  unfold cutoffGrowth
  omega

theorem cutoffStep_le_mul (rank K H C E : ℕ) (hc : C ≤ E) (hE : 1 ≤ E) :
    cutoffStep rank K H C ≤ cutoffGrowth rank K H * E := by
  have HG : E ≤ cutoffGrowth rank K H * E := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right E (cutoffGrowth_positive rank K H)
  have HB : cutBudget rank 0 K H ≤ cutBudget rank 0 K H * E := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (cutBudget rank 0 K H) hE
  apply max_le (hc.trans HG)
  rw [cutBudget_affine]
  have HA := Nat.mul_le_mul_left (2 * rank * K) hc
  unfold cutoffGrowth
  nlinarith only [HA, HB]

theorem stageBudget_positive (rank K H initial stage : ℕ) : 1 ≤ stageBudget rank K H initial stage := by
  have HP := Nat.one_le_pow stage _ (cutoffGrowth_positive rank K H)
  unfold stageBudget
  nlinarith

theorem stageBudget_succ (rank K H initial stage : ℕ) :
    stageBudget rank K H initial (stage + 1) = cutoffGrowth rank K H * stageBudget rank K H initial stage := by
  unfold stageBudget
  rw [pow_succ']
  exact Nat.mul_assoc _ _ _

theorem initial_le_stageBudget (rank K H initial stage : ℕ) : initial ≤ stageBudget rank K H initial stage := by
  have HP := Nat.one_le_pow stage _ (cutoffGrowth_positive rank K H)
  unfold stageBudget
  nlinarith

theorem stageBudget_mono {i j : ℕ} (rank K H initial : ℕ) (hij : i ≤ j) :
    stageBudget rank K H initial i ≤ stageBudget rank K H initial j :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (cutoffGrowth_positive rank K H) hij)

theorem step_le_budget_succ (rank K H initial stage : ℕ) {actualRank actualK actualH C : ℕ}
    (hr : actualRank ≤ rank) (hk : actualK ≤ K) (hh : actualH ≤ H)
    (hc : C ≤ stageBudget rank K H initial stage) :
    cutoffStep actualRank actualK actualH C ≤ stageBudget rank K H initial (stage + 1) := by
  apply (cutoffStep_mono hr hk hh (Nat.le_refl C)).trans
  rw [stageBudget_succ]
  exact cutoffStep_le_mul rank K H C _ hc (stageBudget_positive rank K H initial stage)

theorem step_le_uniform (rank K H initial stages : ℕ) {stage actualRank actualK actualH C : ℕ}
    (hs : stage < stages) (hr : actualRank ≤ rank) (hk : actualK ≤ K) (hh : actualH ≤ H)
    (hc : C ≤ stageBudget rank K H initial stage) :
    cutoffStep actualRank actualK actualH C ≤ stageBudget rank K H initial stages :=
  (step_le_budget_succ rank K H initial stage hr hk hh hc).trans
    (stageBudget_mono rank K H initial (Nat.succ_le_of_lt hs))

theorem cutoffIteration_le (rank K H initial stage : ℕ) :
    cutoffIteration rank K H initial stage ≤ stageBudget rank K H initial stage := by
  induction stage with
  | zero => simp only [cutoffIteration, stageBudget, pow_zero, one_mul]; omega
  | succ stage ih => exact step_le_budget_succ rank K H initial stage le_rfl le_rfl le_rfl ih

theorem cutoffGrowth_binary {rank K H : List Bool → ℕ}
    (hr : BinaryFn rank) (hk : BinaryFn K) (hh : BinaryFn H) :
    BinaryFn (fun q => cutoffGrowth (rank q) (K q) (H q)) :=
  ((((BinaryFn.const 2).mul hr).mul hk).add
    (cutBudget_binary hr (BinaryFn.const 0) hk hh)).add (BinaryFn.const 1)

theorem stageBudget_binary {rank K H initial stages : List Bool → ℕ}
    (hr : BinaryFn rank) (hk : BinaryFn K) (hh : BinaryFn H) (hi : BinaryFn initial) (hs : UnaryFn stages) :
    BinaryFn (fun q => stageBudget (rank q) (K q) (H q) (initial q) (stages q)) :=
  ((cutoffGrowth_binary hr hk hh).powUnary hs).mul (hi.add (BinaryFn.const 1))

end LeanCanny.Algebra.CoefficientCoordinateDyadicBounds

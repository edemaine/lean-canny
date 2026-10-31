/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralParameterExtension
public import LeanCanny.Algebra.MonicParameterPowerSchedule
public import LeanCanny.Algebra.CoordinatePowerRename

/-! # One odd-power schedule for uniformly bounded integral scalar prefixes

Canonical representatives have degree at most m*(N-1). A global birth cap
therefore fixes all scalar and physical powers before root labels are read.
Old scalar powers are preserved by the new-head coordinate layout.
-/

@[expose] public section
namespace LeanCanny.Algebra.UniformIntegralPowerSchedule
open LeanCanny.Encoding
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def cap (S N : ℕ) : ℕ := S * (N - 1)
def birth (S N m : ℕ) : ℕ := MonicParameterPowerSchedule.weight N (cap S N) m
def weights (S N m : ℕ) (i : Fin m) : ℕ := birth S N (m - 1 - i.val)
def coefficientBound (S N m : ℕ) : ℕ := if m = 0 then 0 else birth S N (m - 1) * cap S N
def physical (S N m : ℕ) : ℕ := (2 * cap S N + 1) * birth S N (m - 1)

theorem birth_pos (S N m : ℕ) : 0 < birth S N m := MonicParameterPowerSchedule.weight_pos _ _ _
theorem birth_odd (S N m : ℕ) : Odd (birth S N m) := MonicParameterPowerSchedule.weight_odd _ _ _

theorem birth_le (S N m : ℕ) (hm : m ≤ S) : birth S N m ≤ birth S N S :=
  MonicParameterPowerSchedule.weight_mono _ _ hm

theorem birth_bits (S N m : ℕ) (hm : m ≤ S) :
    (birth S N m).size ≤ (MonicParameterPowerSchedule.ratio N (cap S N)).size * S + 1 :=
  (MonicParameterPowerSchedule.weight_bits N (cap S N) m).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hm) 1)

theorem weights_pos (S N m : ℕ) (i : Fin m) : 0 < weights S N m i := birth_pos _ _ _
theorem weights_odd (S N m : ℕ) (i : Fin m) : Odd (weights S N m i) := birth_odd _ _ _

theorem head (S N m : ℕ) : weights S N (m + 1) 0 = birth S N m := by simp [weights]

theorem old (S N m : ℕ) (i : Fin m) : weights S N (m + 1) i.succ = weights S N m i := by
  unfold weights
  congr 1
  have := i.isLt
  simp only [Fin.val_succ]
  omega

def embed {a m : ℕ} (h : a ≤ m) (i : Fin a) : Fin m := ⟨m - a + i.val, by omega⟩

theorem old_embed (S N : ℕ) {a m : ℕ} (h : a ≤ m) (i : Fin a) :
    weights S N m (embed h i) = weights S N a i := by
  unfold weights
  congr 1
  dsimp only [embed]
  have := i.isLt
  omega

theorem weights_le (S N m : ℕ) (i : Fin m) : weights S N m i ≤ birth S N (m - 1) :=
  MonicParameterPowerSchedule.weight_mono _ _ (Nat.sub_le _ _)

theorem cap_le (S N m : ℕ) (hm : m ≤ S) : m * (N - 1) ≤ cap S N := Nat.mul_le_mul_right _ hm

theorem dominates (S N m : ℕ) : N * coefficientBound S N m < birth S N m := by
  by_cases hm : m = 0
  · subst m
    simp [coefficientBound, birth, MonicParameterPowerSchedule.weight]
  · rw [coefficientBound, ite_eq_right hm]
    have H := MonicParameterPowerSchedule.dominates N (cap S N) (m - 1) N le_rfl
    have HE : m - 1 + 1 = m := by omega
    simpa only [birth, HE] using H

theorem physical_pos (S N m : ℕ) : 0 < physical S N m :=
  Nat.mul_pos (by omega) (birth_pos _ _ _)

theorem physical_odd (S N m : ℕ) : Odd (physical S N m) :=
  (show Odd (2 * cap S N + 1) from ⟨cap S N, rfl⟩).mul (birth_odd _ _ _)

theorem physical_dominates (S N m : ℕ) : birth S N (m - 1) * cap S N < physical S N m := by
  have H : cap S N < 2 * cap S N + 1 := by omega
  exact (Nat.mul_lt_mul_of_pos_left H (birth_pos _ _ _)).trans_eq (Nat.mul_comm _ _)

theorem physical_le (S N m : ℕ) (hm : m ≤ S + 1) :
    physical S N m ≤ (2 * cap S N + 1) * birth S N S :=
  Nat.mul_le_mul_left _ (birth_le S N (m - 1) (by omega))

variable {A : Type*} [CommRing A] {m N : ℕ}

theorem coefficient_degree (S : ℕ) (hm : m ≤ S) (b : IntegralCoordinateBasis A m N)
    (p : Polynomial A) (d i : ℕ) :
    (CoordinatePowerSubstitution.substitute (weights S N m)
      ((PaddedIntegralParameterExtension.equation b p d).coeff i)).totalDegree ≤ coefficientBound S N m := by
  have HD := PaddedIntegralParameterExtension.equation_coefficient_degree b p d i
  by_cases hz : m = 0
  · subst m
    rw [coefficientBound, ite_eq_left rfl]
    apply (CoordinatePowerSubstitution.degree_le _ _ 0 (fun i => Fin.elim0 i)).trans
    simp
  · rw [coefficientBound, ite_eq_right hz]
    exact (CoordinatePowerSubstitution.degree_le _ _ _ (weights_le S N m)).trans
      (Nat.mul_le_mul_left _ (HD.trans (cap_le S N m hm)))

theorem scalar_lower_degree (S : ℕ) (hm : m ≤ S) (hN : 0 < N) (b : IntegralCoordinateBasis A m N)
    (p : Polynomial A) (d : ℕ) :
    (MonicParameterRows.lower (PaddedIntegralParameterExtension.equation b p d) N (weights S N m) (birth S N m)).totalDegree <
      N * birth S N m :=
  MonicParameterRows.lower_degree _ N (coefficientBound S N m) _ _ hN (dominates S N m)
    (coefficient_degree S hm b p d)

theorem scalar_infinity {K : Type*} [Field K] (φ : ℤ →+* K) (S : ℕ) (hm : m ≤ S) (hN : 0 < N)
    (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (y : Option (Fin m ⊕ Unit) → K) (hy : y none = 0) :
    (WeightedHomogenization.homogenize (fun _ => 1) (N * birth S N m)
      (MonicParameterRows.row (PaddedIntegralParameterExtension.equation b p d) N (weights S N m) (birth S N m))).eval₂ φ y =
      y (some (Sum.inr ())) ^ (N * birth S N m) :=
  MonicParameterRows.eval_infinity φ _ N (coefficientBound S N m) _ _ hN (dominates S N m)
    (coefficient_degree S hm b p d) y hy

theorem physical_representative_degree (S : ℕ) (hm : m ≤ S) (b : IntegralCoordinateBasis A m N) (a : A) :
    (CoordinatePowerSubstitution.substitute (weights S N m) (b.representative a)).totalDegree < physical S N m := by
  exact ((CoordinatePowerSubstitution.degree_le _ _ _ (weights_le S N m)).trans
    (Nat.mul_le_mul_left _ ((b.representative_degree a).trans (cap_le S N m hm)))).trans_lt
      (physical_dominates S N m)

theorem physical_ancestor_degree (S : ℕ) {a : ℕ} (h : a ≤ m) (ha : a ≤ S)
    (b : IntegralCoordinateBasis A a N) (x : A) :
    (CoordinatePowerSubstitution.substitute (weights S N m)
      (MvPolynomial.rename (embed h) (b.representative x))).totalDegree < physical S N a := by
  rw [CoordinatePowerSubstitution.rename]
  have HE : weights S N m ∘ embed h = weights S N a := funext (old_embed S N h)
  rw [HE]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans_lt (physical_representative_degree S ha b x)

theorem cap_binary {S N : List Bool → ℕ} (hS : UnaryFn S) (hN : BinaryFn N) :
    BinaryFn (fun c => cap (S c) (N c)) := (BinaryFn.ofUnary hS).mul (hN.sub (BinaryFn.const 1))

theorem birth_binary {S N m : List Bool → ℕ} (hS : UnaryFn S) (hN : BinaryFn N) (hm : UnaryFn m) :
    BinaryFn (fun c => birth (S c) (N c) (m c)) := MonicParameterPowerSchedule.weight_binary hN (cap_binary hS hN) hm

theorem physical_binary {S N m : List Bool → ℕ} (hS : UnaryFn S) (hN : BinaryFn N) (hm : UnaryFn m) :
    BinaryFn (fun c => physical (S c) (N c) (m c)) :=
  (((BinaryFn.const 2).mul (cap_binary hS hN)).add (BinaryFn.const 1)).mul
    (birth_binary hS hN (hm.sub (UnaryFn.const 1)))

def age (m : List Bool → ℕ) (q : List Bool) : ℕ :=
  m (pairFst q) - 1 - min (Nat.fromBitsLE (pairSnd q)) (m (pairFst q))

theorem age_unary {m : List Bool → ℕ} (hm : UnaryFn m) : UnaryFn (age m) :=
  (hm.lift.sub (UnaryFn.const 1)).sub (UnaryFn.fromBitsLE_min pairSnd_mem_FP hm.lift)

def power (S N m : List Bool → ℕ) (q : List Bool) : ℕ := birth (S (pairFst q)) (N (pairFst q)) (age m q)

theorem power_binary {S N m : List Bool → ℕ} (hS : UnaryFn S) (hN : BinaryFn N) (hm : UnaryFn m) :
    BinaryFn (power S N m) := birth_binary (hS.comp pairFst_mem_FP) (hN.comp pairFst_mem_FP) (age_unary hm)

theorem power_packet (S N m : List Bool → ℕ) (c : List Bool) (i : Fin (m c)) :
    power S N m (pair c (BinaryNatCode.encode i.val)) = weights (S c) (N c) (m c) i := by
  simp only [power, age, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    min_eq_left i.isLt.le, weights]

end LeanCanny.Algebra.UniformIntegralPowerSchedule

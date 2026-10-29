/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerTower

/-! # Coefficient mass bounds for complete affine power towers

Raising multiplier variables to any power preserves their unit mass. The
same bound therefore applies to powered gradients and linear inactive rows.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffinePowerTower
open MvPolynomial FlatAffineCriticalTower FlatAffineCriticalStage
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

lemma height_mass (t : Fin k) (a : Fin n → ℤ) (U : ℕ) (ha : ∀ i, (a i).natAbs ≤ U) :
    MvMass.mass (height t a) ≤ n * U :=
  AffineHeightPolynomial.mass_le a (current t) U ha

lemma level_mass (t : Fin k) (b : Level n t.val ℤ) (U B : ℕ) (hb : b.Bounded U B) :
    MvMass.mass (levelPolynomial t b) ≤ max B (2 * n * U) := by
  cases b with
  | constant c =>
    simpa only [levelPolynomial, levelLinear, levelConstant, zero_add, MvMass.C] using
      hb.trans (Nat.le_max_left B (2 * n * U))
  | height j a =>
    simp only [levelPolynomial, levelLinear, levelConstant, map_zero, add_zero]
    exact (height_mass _ a U hb).trans
      ((by nlinarith : n * U ≤ 2 * n * U).trans (Nat.le_max_right _ _))
  | midpoint l r a =>
    simp only [levelPolynomial, levelLinear, levelConstant, map_zero, add_zero]
    exact (AffineHeightPolynomial.midpoint_mass a _ _ U hb).trans (Nat.le_max_right _ _)

lemma gradient_mass (p : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (t : Fin k) (U : ℕ)
    (ha : ∀ r i, (a t r i).natAbs ≤ U) (i : Fin n) :
    MvMass.mass (gradient p D a t i) ≤ p.totalDegree * MvMass.mass p + (n + 1) * U := by
  apply (MvMass.sub_le _ _).trans
  apply Nat.add_le_add
  · exact (MvMass.rename_le _ _).trans (MvMass.pderiv_le _ _)
  · apply (MvMass.sum_le _ _).trans
    calc
      _ ≤ ∑ _r : Fin (n + 1), U := Finset.sum_le_sum fun r _ => by
        apply (MvMass.mul_le _ _).trans
        have hx : MvMass.mass (X (multiplier t r) ^ (D - 1) : MvPolynomial (Index n k) ℤ) ≤ 1 := by
          simpa only [MvMass.X, one_pow] using MvMass.pow_le (X (multiplier t r)) (D - 1)
        exact (Nat.mul_le_mul_left _ hx).trans (by simpa only [MvMass.C, Nat.mul_one] using ha r i)
      _ = (n + 1) * U := by simp

lemma row_mass (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (s : Fin k → Finset (Fin n))
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (b : (t : Fin k) → Fin n → Level n t.val ℤ)
    (t : Fin k) (U B : ℕ) (ha : ∀ r i, (a t r i).natAbs ≤ U)
    (hb : ∀ i, (b t i).Bounded U B) (j : Variables n) :
    MvMass.mass (row p D s a b t j) ≤ massBound p U (max B (2 * n * U)) := by
  cases j with
  | inl i =>
    exact (gradient_mass p D a t U ha i).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _))
  | inr r =>
    refine Fin.cases ?_ (fun j => ?_) r
    · exact (MvMass.rename_le _ _).trans ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _))
    · simp only [row, Fin.cases_succ]
      split_ifs
      · exact (MvMass.sub_le _ _).trans ((Nat.add_le_add (height_mass _ _ U (ha j.succ))
          (level_mass t (b t j) U B (hb j))).trans ((Nat.le_succ _).trans (Nat.le_max_right _ _)))
      · rw [MvMass.X]
        exact (by omega : 1 ≤ n * U + max B (2 * n * U) + 1).trans (Nat.le_max_right _ _)

lemma mass_le (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (s : Fin k → Finset (Fin n))
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (b : (t : Fin k) → Fin n → Level n t.val ℤ)
    (U B : ℕ) (ha : ∀ t r i, (a t r i).natAbs ≤ U) (hb : ∀ t i, (b t i).Bounded U B)
    (j : Index n k) : MvMass.mass (system p D s a b j) ≤ massBound p U (max B (2 * n * U)) :=
  row_mass p D s a b _ U B (ha _) (hb _) _

lemma massBound_le_four (p : MvPolynomial (Fin n) ℤ) (U T : ℕ) (hT : 1 ≤ T)
    (hp : MvMass.mass p ≤ T) (hd : p.totalDegree * MvMass.mass p ≤ T) (hu : (n + 1) * U ≤ T) :
    massBound p U (max U (2 * n * U)) ≤ 4 * T := by
  have hn : n * U ≤ T := (Nat.mul_le_mul_right U (Nat.le_succ n)).trans hu
  have hU : U ≤ T := by rw [Nat.add_mul, one_mul] at hu; omega
  have ht : 2 * n * U ≤ 2 * T := by nlinarith
  unfold massBound
  omega

end LeanCanny.Algebra.FlatAffinePowerTower

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FiniteCoordinateAnnihilator

/-! # Bounded projected zero sets of integer polynomial systems

The sum of squares preserves a system's real zero set, so finiteness of one
coordinate image gives a bounded integer annihilator without a finite-fiber
or regularity hypothesis.
-/

@[expose] public section
namespace LeanCanny.Geometry.SystemCoordinateBounds
open scoped Classical BigOperators
open MvPolynomial Set LeanCanny.Algebra

variable {m n : ℕ}

noncomputable def energy (q : Fin m → MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin n) ℤ :=
  ∑ j, q j ^ 2

theorem eval_energy_zero_iff (q : Fin m → MvPolynomial (Fin n) ℤ) (x : Fin n → ℝ) :
    (energy q).eval₂ (Int.castRingHom ℝ) x = 0 ↔
      ∀ j, (q j).eval₂ (Int.castRingHom ℝ) x = 0 := by
  simp only [energy, eval₂_sum, eval₂_pow, Finset.sum_sq_eq_zero_iff, Finset.mem_univ,
    forall_const]

theorem energy_degree (q : Fin m → MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ D) : (energy q).totalDegree ≤ 2 * D := by
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (hD j))

theorem energy_mass (q : Fin m → MvPolynomial (Fin n) ℤ) (b : ℕ)
    (hb : ∀ j, MvMass.mass (q j) ≤ 2 ^ b) : MvMass.mass (energy q) ≤ 2 ^ (m.size + 2 * b) := by
  calc
    _ ≤ ∑ j : Fin m, MvMass.mass (q j ^ 2) := MvMass.sum_le _ _
    _ ≤ ∑ _j : Fin m, (2 ^ b) ^ 2 := Finset.sum_le_sum fun j _ =>
      (MvMass.pow_le _ _).trans (Nat.pow_le_pow_left (hb j) 2)
    _ = m * (2 ^ b) ^ 2 := by simp
    _ ≤ 2 ^ m.size * (2 ^ b) ^ 2 := Nat.mul_le_mul_right _ (Nat.lt_size_self m).le
    _ = _ := by rw [← pow_mul, ← pow_add, Nat.mul_comm b 2]

theorem exists_bounded (q : Fin m → MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ D) (hb : ∀ j, MvMass.mass (q j) ≤ 2 ^ b)
    (i : Fin n) (hfinite : {t : ℝ | ∃ x : Fin n → ℝ,
      (∀ j, (q j).eval₂ (Int.castRingHom ℝ) x = 0) ∧ x i = t}.Finite) :
    ∃ p : Polynomial ℤ, p ≠ 0 ∧
      p.natDegree ≤ CoerciveCoordinateEliminant.columnBound n (2 * D) ∧
      coefficientMass p < 2 ^ CoerciveRadiusBits.massExponent n (2 * D) (m.size + 2 * b) ∧
      ∀ x : Fin n → ℝ, (∀ j, (q j).eval₂ (Int.castRingHom ℝ) x = 0) →
        p.eval₂ (Int.castRingHom ℝ) (x i) = 0 := by
  obtain ⟨p, hp, hd, hm, hann⟩ := FiniteCoordinateAnnihilator.exists_bounded_bits
    (energy q) (2 * D) (m.size + 2 * b) (energy_degree q D hD) (energy_mass q b hb) i
    (by simpa only [eval_energy_zero_iff] using hfinite)
  exact ⟨p, hp, hd, hm, fun x hx => hann x ((eval_energy_zero_iff q x).mpr hx)⟩

end LeanCanny.Geometry.SystemCoordinateBounds

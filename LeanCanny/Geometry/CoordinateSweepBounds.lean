/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FiniteCoordinateAnnihilator
public import LeanCanny.Geometry.PolynomialHypersurfaceSweep
public import LeanCanny.Algebra.PartialDerivativeDegree

/-! # Bounded exceptional values for integer coordinate sweeps

On a regular integer hypersurface, a sum of squares defines its coordinate
critical locus. Its projected zero set is finite by the qualitative critical
value theorem. Constrained coercive elimination gives one integer exceptional
polynomial with degree and coefficient bounds calculated from source bounds.
-/

@[expose] public section
namespace LeanCanny.Geometry.CoordinateSweepBounds
open scoped Classical BigOperators
open MvPolynomial Set LeanCanny.Algebra
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

noncomputable def energy (q : MvPolynomial (Fin n) ℤ) (base : Fin n) : MvPolynomial (Fin n) ℤ :=
  q ^ 2 + ∑ i ∈ Finset.univ.erase base, pderiv i q ^ 2

theorem eval_energy_zero_iff (q : MvPolynomial (Fin n) ℤ) (base : Fin n) (x : Fin n → ℝ) :
    (energy q base).eval₂ (Int.castRingHom ℝ) x = 0 ↔
      q.eval₂ (Int.castRingHom ℝ) x = 0 ∧
      ∀ i, i ≠ base → (pderiv i q).eval₂ (Int.castRingHom ℝ) x = 0 := by
  simp only [energy, eval₂_add, eval₂_sum, eval₂_pow]
  rw [add_eq_zero_iff_of_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _), sq_eq_zero_iff, Finset.sum_sq_eq_zero_iff]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]

theorem energy_degree (q : MvPolynomial (Fin n) ℤ) (base : Fin n) (D : ℕ)
    (hD : q.totalDegree ≤ D) : (energy q base).totalDegree ≤ 2 * D := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hD)
  · apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2
      ((PartialDerivativeDegree.degree_le q i).trans ((Nat.sub_le _ _).trans hD)))

def energyMassExponent (n D b : ℕ) : ℕ := (n + 1).size + 2 * (D.size + b)

theorem energy_mass (q : MvPolynomial (Fin n) ℤ) (base : Fin n) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b) :
    MvMass.mass (energy q base) ≤ 2 ^ energyMassExponent n D b := by
  have hq : MvMass.mass q ≤ 2 ^ (D.size + b) :=
    hb.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left b D.size))
  have hp (i : Fin n) : MvMass.mass (pderiv i q) ≤ 2 ^ (D.size + b) := by
    apply (MvMass.pderiv_le q i).trans
    calc
      _ ≤ D * 2 ^ b := Nat.mul_le_mul hD hb
      _ ≤ 2 ^ D.size * 2 ^ b := Nat.mul_le_mul_right _ (Nat.lt_size_self D).le
      _ = _ := (pow_add _ _ _).symm
  have he : MvMass.mass (energy q base) ≤ (n + 1) * (2 ^ (D.size + b)) ^ 2 := by
    apply (MvMass.add_le _ _).trans
    apply (Nat.add_le_add (MvMass.pow_le q 2) (MvMass.sum_le _ _)).trans
    calc
      _ ≤ (2 ^ (D.size + b)) ^ 2 + ∑ _i ∈ Finset.univ.erase base, (2 ^ (D.size + b)) ^ 2 :=
        Nat.add_le_add (Nat.pow_le_pow_left hq 2) (Finset.sum_le_sum fun i _ =>
          (MvMass.pow_le _ _).trans (Nat.pow_le_pow_left (hp i) 2))
      _ ≤ (2 ^ (D.size + b)) ^ 2 + ∑ _i : Fin n, (2 ^ (D.size + b)) ^ 2 :=
        Nat.add_le_add_left (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)) _
      _ = _ := by simp [Nat.add_mul, Nat.add_comm]
  calc
    _ ≤ (n + 1) * (2 ^ (D.size + b)) ^ 2 := he
    _ ≤ 2 ^ (n + 1).size * (2 ^ (D.size + b)) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.lt_size_self (n + 1)).le
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; unfold energyMassExponent; omega

/-- Regularity of the whole zero set guarantees finitely many projected
critical values. This step needs no arithmetic estimate on its witness. -/
theorem finite_critical_values (q : MvPolynomial (Fin n) ℤ) (base : Fin n)
    (hregular : ∀ x : Fin n → ℝ, q.eval₂ (Int.castRingHom ℝ) x = 0 →
      Function.Surjective (fderiv ℝ (fun y => q.eval₂ (Int.castRingHom ℝ) y) x)) :
    {t : ℝ | ∃ x : Fin n → ℝ, (energy q base).eval₂ (Int.castRingHom ℝ) x = 0 ∧ x base = t}.Finite := by
  let qR := q.map (Int.castRingHom ℝ)
  obtain ⟨d, hd, hm⟩ := CoordinateCriticalValues.exists_annihilator qR base
  apply (Polynomial.finite_setOfPred_isRoot hd).subset
  rintro t ⟨x, hx, rfl⟩
  obtain ⟨hq, hother⟩ := (eval_energy_zero_iff q base x).mp hx
  have hb : (pderiv base q).eval₂ (Int.castRingHom ℝ) x ≠ 0 := by
    intro hb
    have hall (i : Fin n) : (pderiv i q).eval₂ (Int.castRingHom ℝ) x = 0 := by
      by_cases hi : i = base
      · simpa only [hi] using hb
      · exact hother i hi
    have hz := (PolynomialCalculus.critical_iff (Int.castRingHom ℝ) q x).mpr hall
    obtain ⟨v, hv⟩ := hregular x hq 1
    rw [hz] at hv
    exact zero_ne_one hv
  have he := CoordinateCriticalValues.eval_annihilator qR base d hm x
    (by simpa only [qR, aeval_def, Algebra.algebraMap_self, eval₂_id, eval_map] using hq)
    (by simpa only [qR, aeval_def, Algebra.algebraMap_self, eval₂_id, pderiv_map, eval_map] using hb)
    (fun i hi => by
      simpa only [qR, aeval_def, Algebra.algebraMap_self, eval₂_id, pderiv_map, eval_map] using hother i hi)
  change d.eval (x base) = 0
  simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using he

/-- The exceptional factor has bounds using only dimension, degree, and a
coefficient-mass exponent. Outside its roots, the combined derivative is onto. -/
theorem exists_bounded_exceptional (q : MvPolynomial (Fin n) ℤ) (base : Fin n) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b)
    (hregular : ∀ x : Fin n → ℝ, q.eval₂ (Int.castRingHom ℝ) x = 0 →
      Function.Surjective (fderiv ℝ (fun y => q.eval₂ (Int.castRingHom ℝ) y) x)) :
    ∃ d : Polynomial ℤ, d ≠ 0 ∧
      d.natDegree ≤ CoerciveCoordinateEliminant.columnBound n (2 * D) ∧
      coefficientMass d < 2 ^ CoerciveRadiusBits.massExponent n (2 * D) (energyMassExponent n D b) ∧
      ∀ x : Fin n → ℝ, q.eval₂ (Int.castRingHom ℝ) x = 0 →
        d.eval₂ (Int.castRingHom ℝ) (x base) ≠ 0 →
        Function.Surjective (fderiv ℝ
          (HypersurfaceSweep.combined (fun y => q.eval₂ (Int.castRingHom ℝ) y) (fun y => y base)) x) := by
  obtain ⟨d, hd, hdeg, hmass, hann⟩ := FiniteCoordinateAnnihilator.exists_bounded_bits
    (energy q base) (2 * D) (energyMassExponent n D b) (energy_degree q base D hD)
    (energy_mass q base D b hD hb) base (finite_critical_values q base hregular)
  refine ⟨d, hd, hdeg, hmass, ?_⟩
  intro x hx hdx
  have hex : ∃ i, i ≠ base ∧ (pderiv i q).eval₂ (Int.castRingHom ℝ) x ≠ 0 := by
    by_contra h
    push Not at h
    exact hdx (hann x ((eval_energy_zero_iff q base x).mpr ⟨hx, h⟩))
  obtain ⟨i, hi, hp⟩ := hex
  have hs := PolynomialHypersurfaceSweep.surjective_combined_of_partial
    (q.map (Int.castRingHom ℝ)) base i x hi
    (by simpa only [pderiv_map, eval_map] using hp)
  simpa only [eval_map] using hs

end LeanCanny.Geometry.CoordinateSweepBounds

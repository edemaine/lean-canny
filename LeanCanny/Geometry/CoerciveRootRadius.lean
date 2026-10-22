/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoerciveCoordinateEliminant
public import LeanCanny.Algebra.CoerciveRadiusBits
public import LeanCanny.Geometry.CoerciveAnnihilatorLimit
public import LeanCanny.Geometry.CoerciveApproximation

/-! # An explicit root radius from the original integer polynomial

The integer coordinate annihilants are constructed internally. Their lowest
parameter coefficients bound a real root whenever one exists. A corresponding
penalty bound turns root existence into bounded approximate critical sampling
with just one positive perturbation parameter.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace LeanCanny.Geometry.CoerciveRootRadius
open scoped Classical BigOperators
open LeanCanny.Algebra
open CoercivePolynomialSampling

variable {n : ℕ}

theorem exists_root_bounded (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (hroot : ∃ x : Fin n → ℝ, q.eval₂ (Int.castRingHom ℝ) x = 0) :
    ∃ a : Fin n → ℝ, q.eval₂ (Int.castRingHom ℝ) a = 0 ∧
      ∀ i, |a i| < (CoerciveCoordinateEliminant.massBound q D : ℝ) + 1 := by
  obtain ⟨x0, hx0⟩ := hroot
  choose H hH _hDs _hDt hM hvanish using
    fun i => CoerciveCoordinateEliminant.exists_annihilator q D hD i
  have hann (i : Fin n) : CoerciveAnnihilatorLimit.IsCoordinateAnnihilator
      (q.map (Int.castRingHom ℝ)) D i (H i) := by
    intro s _hs x hx
    exact hvanish i s x hx
  have hb (i : Fin n) : coefficientMass (H i).trailingCoeff ≤
      CoerciveCoordinateEliminant.massBound q D :=
    (NestedMass.coeff_le (H i) (H i).natTrailingDegree).trans (hM i)
  have hx0' : MvPolynomial.eval x0 (q.map (Int.castRingHom ℝ)) = 0 := by
    simpa only [MvPolynomial.eval_map] using hx0
  obtain ⟨a, ha, hb⟩ := CoerciveAnnihilatorLimit.exists_root_bounded
    (q.map (Int.castRingHom ℝ)) D x0 hx0' H hH hann
    (CoerciveCoordinateEliminant.massBound q D) hb
  exact ⟨a, by simpa only [MvPolynomial.eval_map] using ha, hb⟩

noncomputable def penaltyBound (q : MvPolynomial (Fin n) ℤ) (D : ℕ) : ℕ :=
  n * (CoerciveCoordinateEliminant.massBound q D + 1) ^ (2 * D + 2)

theorem exists_root_penalty_bounded (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (hroot : ∃ x : Fin n → ℝ, q.eval₂ (Int.castRingHom ℝ) x = 0) :
    ∃ a : Fin n → ℝ, q.eval₂ (Int.castRingHom ℝ) a = 0 ∧
      penalty D a ≤ (penaltyBound q D : ℝ) := by
  obtain ⟨a, ha, hb⟩ := exists_root_bounded q D hD hroot
  refine ⟨a, ha, ?_⟩
  unfold penalty
  calc
    ∑ i : Fin n, a i ^ (2 * D + 2) ≤
        ∑ _i : Fin n, ((CoerciveCoordinateEliminant.massBound q D : ℝ) + 1) ^ (2 * D + 2) := by
      apply Finset.sum_le_sum
      intro i _
      have he : a i ^ (2 * D + 2) = |a i| ^ (2 * D + 2) := by
        rw [← abs_pow, abs_of_nonneg (power_nonneg D _)]
      rw [he]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb i).le (2 * D + 2)
    _ = (penaltyBound q D : ℝ) := by simp [penaltyBound]

theorem root_iff_approximate_critical_samples (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) :
    (∃ x : Fin n → ℝ, q.eval₂ (Int.castRingHom ℝ) x = 0) ↔
      ∀ s : ℝ, 0 < s → ∃ x, CoerciveApproximation.Sample
        (q.map (Int.castRingHom ℝ)) D (penaltyBound q D : ℝ) s x := by
  rw [← CoerciveApproximation.root_iff_samples]
  constructor
  · intro h
    obtain ⟨a, ha, hb⟩ := exists_root_penalty_bounded q D hD h
    exact ⟨a, by simpa only [MvPolynomial.eval_map] using ha, hb⟩
  · rintro ⟨a, ha, _hb⟩
    exact ⟨a, by simpa only [MvPolynomial.eval_map] using ha⟩

/-- The same characterization on an eventual positive interval is the form
needed by symbolic infinitesimal sign procedures. -/
theorem root_iff_eventually_critical_samples (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) :
    (∃ x : Fin n → ℝ, q.eval₂ (Int.castRingHom ℝ) x = 0) ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ → ∃ x, CoerciveApproximation.Sample
        (q.map (Int.castRingHom ℝ)) D (penaltyBound q D : ℝ) s x := by
  rw [← CoerciveApproximation.root_iff_eventually_samples]
  constructor
  · intro h
    obtain ⟨a, ha, hb⟩ := exists_root_penalty_bounded q D hD h
    exact ⟨a, by simpa only [MvPolynomial.eval_map] using ha, hb⟩
  · rintro ⟨a, ha, _hb⟩
    exact ⟨a, by simpa only [MvPolynomial.eval_map] using ha⟩

/-- The radius exponent uses only dimension, a degree allowance, and a mass
allowance exponent, rather than an exact source-mass computation. -/
theorem exists_root_exp_bounded (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b)
    (hroot : ∃ x : Fin n → ℝ, q.eval₂ (Int.castRingHom ℝ) x = 0) :
    ∃ a : Fin n → ℝ, q.eval₂ (Int.castRingHom ℝ) a = 0 ∧
      ∀ i, |a i| < (2 : ℝ) ^ CoerciveRadiusBits.massExponent n D b := by
  obtain ⟨a, ha, hbound⟩ := exists_root_bounded q D hD hroot
  have hm : (CoerciveCoordinateEliminant.massBound q D : ℝ) + 1 ≤
      (2 : ℝ) ^ CoerciveRadiusBits.massExponent n D b := by
    exact_mod_cast CoerciveRadiusBits.massBound_add_one_le q D b hb
  exact ⟨a, ha, fun i => (hbound i).trans_le hm⟩

/-- Source-budgeted, eventual critical sampling is equivalent to real root
existence. Both numeric exponents have polynomial binary-size bounds in
`CoerciveRadiusBits`; no explicit exponentially long dyadic packet is used. -/
theorem root_iff_eventually_bounded_samples (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b) :
    (∃ x : Fin n → ℝ, q.eval₂ (Int.castRingHom ℝ) x = 0) ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ → ∃ x, CoerciveApproximation.Sample
        (q.map (Int.castRingHom ℝ)) D
        ((2 : ℝ) ^ CoerciveRadiusBits.penaltyExponent n D b) s x := by
  rw [← CoerciveApproximation.root_iff_eventually_samples]
  constructor
  · intro h
    obtain ⟨a, ha, hbound⟩ := exists_root_exp_bounded q D b hD hb h
    refine ⟨a, by simpa only [MvPolynomial.eval_map] using ha, ?_⟩
    exact CoerciveRadiusBits.penalty_le n D b a (fun i => (hbound i).le)
  · rintro ⟨a, ha, _hb⟩
    exact ⟨a, by simpa only [MvPolynomial.eval_map] using ha⟩

end LeanCanny.Geometry.CoerciveRootRadius

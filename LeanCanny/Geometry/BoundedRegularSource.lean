/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.BoundedZeroPerturbation
public import LeanCanny.Geometry.IntegerRegularSource
public import LeanCanny.Geometry.PurePowerSublevelLevels

/-! # A regular pure-power source inside the safe component interval

After scaling the positive perturbation, shift by its interval's lower
endpoint. The existing integer regularization then chooses a tiny positive
level above that shift. The resulting original-scale level remains inside
the safe interval. This constructs regularity without moving to an unrelated
small level of the unshifted perturbed energy.
-/

@[expose] public section
namespace LeanCanny.Geometry.BoundedRegularSource
open MvPolynomial Set LeanCanny.Algebra BoundedZeroSource
open scoped BigOperators

variable {n : ℕ}

noncomputable def lower (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) : MvPolynomial (Fin (n + 4)) ℤ :=
  C ((2 : ℤ) ^ perturbationExponent n D b R) * rename (Fin.castAdd 2) (BoundedZeroSource.polynomial q R) -
    C ((2 : ℤ) ^ penaltyExponent n D R)

def lowMassExponent (n D b R : ℕ) : ℕ := perturbationExponent n D b R + massExponent n b R + penaltyExponent n D R + 1
def sourceMassExponent (n D b R : ℕ) : ℕ := lowMassExponent n D b R + (n + 5).size
def regularizationExponent (n D b R : ℕ) : ℕ :=
  IntegerRegularSource.exponent (n + 3) (powerDegree D) (sourceMassExponent n D b R)

noncomputable def polynomial (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) : MvPolynomial (Fin (n + 4)) ℤ :=
  FermatCriticalHomogenization.polynomial
    (IntegerRegularSource.lower (lower q D b R) (powerDegree D) (sourceMassExponent n D b R))
    (IntegerRegularSource.leading (n + 3) 1 (powerDegree D) (sourceMassExponent n D b R)) (powerDegree D)

noncomputable def level (n D b R : ℕ) : ℝ :=
  (2 : ℝ) ^ penaltyExponent n D R + InfinitesimalSign.dyadic (regularizationExponent n D b R)

noncomputable def originalLevel (n D b R : ℕ) : ℝ := perturbationCoefficient n D b R * level n D b R

theorem originalLevel_window (n D b R : ℕ) :
    tolerance n D b R / 2 ≤ originalLevel n D b R ∧ originalLevel n D b R ≤ tolerance n D b R := by
  have hη : 0 < perturbationCoefficient n D b R :=
    BoundedPositivePerturbation.coefficient_pos (n + 2) (degreeAllowance D) (massExponent n b R) (penaltyExponent n D R)
  have hm : perturbationCoefficient n D b R * 2 ^ penaltyExponent n D R = tolerance n D b R / 2 :=
    BoundedPositivePerturbation.coefficient_mul_pow (n + 2) (degreeAllowance D) (massExponent n b R) (penaltyExponent n D R)
  have hηle : perturbationCoefficient n D b R ≤ tolerance n D b R / 2 :=
    (show perturbationCoefficient n D b R ≤ perturbationCoefficient n D b R * 2 ^ penaltyExponent n D R from
      le_mul_of_one_le_right hη.le (one_le_pow₀ (by norm_num))).trans_eq hm
  have hε := InfinitesimalSign.dyadic_pos (regularizationExponent n D b R)
  have hεle := InfinitesimalSign.dyadic_le_one (regularizationExponent n D b R)
  have hprod := mul_nonneg hη.le hε.le
  have hupper := mul_le_of_le_one_right hη.le hεle
  unfold originalLevel level
  rw [mul_add, hm]
  constructor <;> linarith

theorem powerDegree_gt_one (D : ℕ) : 1 < powerDegree D := by
  unfold powerDegree powerHalfDegree degreeAllowance
  omega

theorem lower_degree (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (hD : q.totalDegree ≤ D) :
    (lower q D b R).totalDegree < powerDegree D := by
  apply (totalDegree_sub _ _).trans_lt
  apply max_lt
  · apply (totalDegree_mul _ _).trans_lt
    simpa only [totalDegree_C, Nat.zero_add] using
      ((totalDegree_rename_le _ _).trans (BoundedZeroSource.degree_bound q D R hD)).trans_lt (degreeAllowance_lt_power D)
  · rw [totalDegree_C]
    exact (by have := powerDegree_gt_one D; omega)

theorem lower_mass (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (hb : MvMass.mass q ≤ 2 ^ b) :
    MvMass.mass (lower q D b R) ≤ 2 ^ lowMassExponent n D b R := by
  have hp := (MvMass.rename_le (Fin.castAdd 2) (BoundedZeroSource.polynomial q R)).trans
    (BoundedZeroSource.mass_bound q b R hb)
  have hscale : MvMass.mass (C ((2 : ℤ) ^ perturbationExponent n D b R) : MvPolynomial (Fin (n + 4)) ℤ) =
      2 ^ perturbationExponent n D b R := by simp only [MvMass.C, Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl]
  have hshift : MvMass.mass (C ((2 : ℤ) ^ penaltyExponent n D R) : MvPolynomial (Fin (n + 4)) ℤ) =
      2 ^ penaltyExponent n D R := by simp only [MvMass.C, Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl]
  have hm := (MvMass.mul_le _ _).trans (Nat.mul_le_mul hscale.le hp)
  rw [← pow_add] at hm
  apply (MvMass.sub_le _ _).trans
  apply (Nat.add_le_add hm hshift.le).trans
  have h1 : 2 ^ (perturbationExponent n D b R + massExponent n b R) ≤
      2 ^ (perturbationExponent n D b R + massExponent n b R + penaltyExponent n D R) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2 ^ penaltyExponent n D R ≤
      2 ^ (perturbationExponent n D b R + massExponent n b R + penaltyExponent n D R) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  unfold lowMassExponent
  rw [pow_succ]
  omega

theorem source_mass (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (hb : MvMass.mass q ≤ 2 ^ b) :
    MvMass.mass (FermatCriticalHomogenization.polynomial (lower q D b R) 1 (powerDegree D)) ≤
      2 ^ sourceMassExponent n D b R :=
  FermatRegularSource.mass_le (lower q D b R) 1 (powerDegree D) (lowMassExponent n D b R)
    (lower_mass q D b R hb) (by simpa only [Int.natAbs_one] using Nat.one_le_two_pow)

theorem regular {L : Type*} [Field L] [Algebra ℚ L] (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b) (x : Fin (n + 4) → L)
    (hx : (polynomial q D b R).eval₂ (Int.castRingHom L) x = 0) :
    ∃ j, (pderiv j (polynomial q D b R)).eval₂ (Int.castRingHom L) x ≠ 0 :=
  IntegerRegularSource.regular (lower q D b R) 1 (powerDegree D) (sourceMassExponent n D b R)
    (lower_degree q D b R hD) (by decide) (powerDegree_gt_one D) (source_mass q D b R hb) x hx

end LeanCanny.Geometry.BoundedRegularSource

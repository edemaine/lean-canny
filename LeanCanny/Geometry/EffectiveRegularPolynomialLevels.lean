/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeRegularity
public import LeanCanny.Algebra.EffectiveInfinitesimalSign
public import LeanCanny.Algebra.CriticalValueIntegerAnnihilator

/-! # Explicit regular-level intervals from integer critical-value annihilants

A nonzero integer polynomial of coefficient mass at most `2^b` has no positive
root at or below `2^(-(b+1))`. Thus any such annihilator of the critical values
gives an explicit regular-level interval, uniformly over all active tubes.

The annihilators and their mass bounds are explicit hypotheses. Constructing
them with bounds in the encoded source size remains a separate obligation.
-/

@[expose] public section

namespace LeanCanny.Algebra.InfinitesimalSign
open Polynomial

theorem eval_ne_zero_le_dyadic (q : ℤ[X]) (b : ℕ) (hq : q ≠ 0)
    (hm : coefficientMass q ≤ 2 ^ b) (x : ℝ) (hx : 0 < x)
    (hsmall : x ≤ dyadic (b + 1)) :
    q.eval₂ (Int.castRingHom ℝ) x ≠ 0 := by
  intro hz
  have hs := integer_sign_eval_le_dyadic q b (b + 1) hm (Nat.lt_succ_self b) x hx hsmall
  rw [hz, sign_zero] at hs
  exact hq (Polynomial.trailingCoeff_eq_zero.mp (sign_eq_zero_iff.mp hs.symm))

end LeanCanny.Algebra.InfinitesimalSign

namespace LeanCanny.Geometry.RegularPolynomialLevels
open LeanCanny.Algebra

variable {ι : Type*} [Fintype ι]

/-- A genuine algebraic obstruction, independent of any feasibility predicate. -/
def IsCriticalValueAnnihilator (p : MvPolynomial ι ℝ) (q : Polynomial ℤ) : Prop :=
  ∀ x : ι → ℝ, fderiv ℝ (fun y => MvPolynomial.aeval y p) x = 0 →
    q.eval₂ (Int.castRingHom ℝ) (MvPolynomial.aeval x p) = 0

theorem exists_integer_annihilator_of_rational (p : MvPolynomial ι ℚ) :
    ∃ q : Polynomial ℤ, q ≠ 0 ∧
      IsCriticalValueAnnihilator (p.map (algebraMap ℚ ℝ)) q := by
  classical
  obtain ⟨q, hq, ha⟩ := CriticalValueAnnihilator.exists_integer_real_annihilator p
  have he : (fun y : ι → ℝ => MvPolynomial.aeval y (p.map (algebraMap ℚ ℝ))) =
      (fun y : ι → ℝ => MvPolynomial.aeval y p) := by
    funext y
    simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map,
      Algebra.algebraMap_self, RingHom.id_comp]
  refine ⟨q, hq, ?_⟩
  intro x hx
  rw [he] at hx
  rw [congrFun he x]
  exact ha x ((PolynomialCalculus.critical_iff (algebraMap ℚ ℝ) p x).mp hx)

theorem surjective_on_dyadic_interval (p : MvPolynomial ι ℝ) (q : Polynomial ℤ)
    (hq : q ≠ 0) (ha : IsCriticalValueAnnihilator p q) (b : ℕ)
    (hm : coefficientMass q ≤ 2 ^ b) (alpha : ℝ) (hp : 0 < alpha)
    (hs : alpha ≤ InfinitesimalSign.dyadic (b + 1)) (x : ι → ℝ)
    (hx : MvPolynomial.aeval x p = alpha) :
    Function.Surjective (fderiv ℝ (fun y => MvPolynomial.aeval y p - alpha) x) := by
  rw [fderiv_sub_const]
  apply surjective_of_ne_zero
  intro hzero
  have hz := ha x hzero
  rw [hx] at hz
  exact InfinitesimalSign.eval_ne_zero_le_dyadic q b hq hm alpha hp hs hz

end LeanCanny.Geometry.RegularPolynomialLevels

namespace LeanCanny.Geometry.TubePolynomial
open LeanCanny.Algebra

variable {ι : Type*} [Fintype ι]

noncomputable def rationalEnergy (p : MvPolynomial ι ℤ)
    (s : Finset (PolynomialPerturbation.Constraint ι)) (epsilon delta : ℚ) :
    MvPolynomial (Coordinate ι) ℚ :=
  (energy p s).map (MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
    (fun i : Parameter => match i with
      | none => 0
      | some false => epsilon
      | some true => delta))

theorem rationalEnergy_map (p : MvPolynomial ι ℤ)
    (s : Finset (PolynomialPerturbation.Constraint ι)) (epsilon delta : ℚ) :
    (rationalEnergy p s epsilon delta).map (algebraMap ℚ ℝ) =
      realEnergy p s (epsilon : ℝ) (delta : ℝ) := by
  have he : (algebraMap ℚ ℝ).comp
      (MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
        (fun i : Parameter => match i with
          | none => 0
          | some false => epsilon
          | some true => delta)) =
        coefficientMap (epsilon : ℝ) (delta : ℝ) 0 := by
    ext i
    · simp
    · cases i with
      | none => simp [coefficientMap, parameters]
      | some b => cases b <;> simp [coefficientMap, parameters]
  simp only [rationalEnergy, realEnergy, MvPolynomial.map_map, he]

/-- Rational tube parameters admit actual integer critical-value annihilants.
No bound on the heights of the resulting annihilants is asserted. -/
theorem exists_integer_energy_annihilators (p : MvPolynomial ι ℤ) (epsilon delta : ℚ) :
    ∃ q : Finset (PolynomialPerturbation.Constraint ι) → Polynomial ℤ,
      (∀ s, q s ≠ 0) ∧ ∀ s, RegularPolynomialLevels.IsCriticalValueAnnihilator
        (realEnergy p s (epsilon : ℝ) (delta : ℝ)) (q s) := by
  classical
  have h := fun s => RegularPolynomialLevels.exists_integer_annihilator_of_rational
    (rationalEnergy p s epsilon delta)
  simp_rw [rationalEnergy_map] at h
  choose q hq ha using h
  exact ⟨q, hq, ha⟩

/-- One explicit closed positive interval works for every active set. -/
theorem common_regular_dyadic_interval (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (q : Finset (PolynomialPerturbation.Constraint ι) → Polynomial ℤ)
    (hq : ∀ s, q s ≠ 0)
    (ha : ∀ s, RegularPolynomialLevels.IsCriticalValueAnnihilator
      (realEnergy p s epsilon delta) (q s)) (b : ℕ)
    (hm : ∀ s, coefficientMass (q s) ≤ 2 ^ b)
    (alpha : ℝ) (hp : 0 < alpha) (hs : alpha ≤ InfinitesimalSign.dyadic (b + 1))
    (s : Finset (PolynomialPerturbation.Constraint ι)) (x : Coordinate ι → ℝ)
    (hx : (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0) :
    Function.Surjective
      (fderiv ℝ (fun y => (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) y) x) := by
  have hv : MvPolynomial.aeval x (realEnergy p s epsilon delta) = alpha := by
    rw [eval_as_realEnergy, sub_eq_zero] at hx
    exact hx
  have hr := RegularPolynomialLevels.surjective_on_dyadic_interval
    (realEnergy p s epsilon delta) (q s) (hq s) (ha s) b (hm s) alpha hp hs x hv
  have he : (fun y => (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) y) =
      (fun y => MvPolynomial.aeval y (realEnergy p s epsilon delta) - alpha) :=
    funext (eval_as_realEnergy p s epsilon delta alpha)
  rw [he]
  exact hr

end LeanCanny.Geometry.TubePolynomial

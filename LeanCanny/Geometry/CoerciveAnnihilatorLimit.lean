/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CoercivePolynomialSampling
public import LeanCanny.Geometry.PolynomialLimitAnnihilator
public import LeanCanny.Algebra.CoerciveCriticalFibers
public import LeanCanny.Algebra.IntegerRootBound

/-! # Root bounds from coordinate annihilants of coercive critical samples

Actual critical-point annihilants pass to the concrete bounded minimizing
sequence. Their nonzero lowest parameter coefficients annihilate the limiting
root and bound its coordinates by their integer coefficient masses. This is a
bridge for supplied annihilants, not an assertion of their arithmetic budgets.
Membership in the actual gradient ideal suffices for the annihilation premise.
-/

@[expose] public section
namespace LeanCanny.Geometry.CoerciveAnnihilatorLimit
open LeanCanny.Algebra
open scoped Classical BigOperators Topology
open Filter Set
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- An integer bivariate polynomial, with the perturbation parameter outermost,
annihilates coordinate `i` at every positive-parameter critical point. -/
def IsCoordinateAnnihilator (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (i : Fin n)
    (H : Polynomial (Polynomial ℤ)) : Prop :=
  ∀ s : ℝ, 0 < s → ∀ x : Fin n → ℝ,
    (∀ j, MvPolynomial.eval x (MvPolynomial.pderiv j (CoerciveCriticalFibers.polynomial q D s)) = 0) →
      PolynomialLimitAnnihilator.value H s (x i) = 0

/-- Substitute a coordinate variable for the inner indeterminate and a real
parameter for the outer indeterminate. -/
noncomputable def coordinatePolynomial (H : Polynomial (Polynomial ℤ)) (s : ℝ) (i : Fin n) :
    MvPolynomial (Fin n) ℝ :=
  H.eval₂ (Polynomial.eval₂RingHom
    (MvPolynomial.C.comp (Int.castRingHom ℝ)) (MvPolynomial.X i)) (MvPolynomial.C s)

lemma eval_coordinatePolynomial (H : Polynomial (Polynomial ℤ)) (s : ℝ) (i : Fin n)
    (x : Fin n → ℝ) :
    MvPolynomial.eval x (coordinatePolynomial H s i) = PolynomialLimitAnnihilator.value H s (x i) := by
  have he : (MvPolynomial.eval x).comp
      (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom
        (MvPolynomial.C.comp (Int.castRingHom ℝ)) (MvPolynomial.X i)) (MvPolynomial.C s)) =
      Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (x i)) s := by
    ext <;> simp
  exact congrArg (fun f : Polynomial (Polynomial ℤ) →+* ℝ => f H) he

/-- An actual ideal certificate supplies the critical-root annihilation relation. -/
theorem isCoordinateAnnihilator_of_ideal (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (i : Fin n)
    (H : Polynomial (Polynomial ℤ))
    (hI : ∀ s : ℝ, 0 < s → coordinatePolynomial H s i ∈
      CoerciveCriticalFibers.generated (fun j => MvPolynomial.pderiv j
        (CoerciveCriticalFibers.polynomial q D s))) : IsCoordinateAnnihilator q D i H := by
  intro s hs x hx
  have hker : CoerciveCriticalFibers.generated (fun j => MvPolynomial.pderiv j
      (CoerciveCriticalFibers.polynomial q D s)) ≤ RingHom.ker (MvPolynomial.eval x) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hx j
  have hz := hker (hI s hs)
  change MvPolynomial.eval x (coordinatePolynomial H s i) = 0 at hz
  rwa [eval_coordinatePolynomial] at hz

/-- The limiting root is annihilated by the nonzero integer lowest-parameter
coefficients of the given actual critical-point annihilants. -/
theorem exists_root_with_annihilants (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (x0 : Fin n → ℝ) (hroot : MvPolynomial.eval x0 q = 0)
    (H : Fin n → Polynomial (Polynomial ℤ)) (hH : ∀ i, H i ≠ 0)
    (hann : ∀ i, IsCoordinateAnnihilator q D i (H i)) :
    ∃ a : Fin n → ℝ, MvPolynomial.eval a q = 0 ∧
      CoercivePolynomialSampling.penalty D a ≤ CoercivePolynomialSampling.penalty D x0 ∧
      (∀ i, (H i).trailingCoeff.eval₂ (Int.castRingHom ℝ) (a i) = 0) ∧
      ∀ i, |a i| < (coefficientMass (H i).trailingCoeff : ℝ) + 1 := by
  obtain ⟨y, a, φ, _hm, hc, _hb, _hcoord, hφ, hlim, ha, hq⟩ :=
    CoercivePolynomialSampling.exists_critical_samples q D x0 hroot
  have htr (i : Fin n) : (H i).trailingCoeff.eval₂ (Int.castRingHom ℝ) (a i) = 0 := by
    apply PolynomialLimitAnnihilator.trailingCoeff_eval_eq_zero (H i)
      (fun k => 1 / (((φ k : ℕ) : ℝ) + 1)) (fun k => y (φ k) i) (a i)
    · intro k
      positivity
    · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    · exact (continuous_apply i).continuousAt.tendsto.comp hlim
    · intro k
      apply hann i _ (by positivity) (y (φ k))
      exact hc (φ k)
  refine ⟨a, hq, ha, htr, ?_⟩
  intro i
  exact abs_root_lt_coefficientMass_add_one (H i).trailingCoeff
    (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (hH i)) (a i) (htr i)

/-- A uniform integer mass allowance on the lowest-parameter coefficients gives
one uniform root radius. The allowance remains an explicit arithmetic premise. -/
theorem exists_root_bounded (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (x0 : Fin n → ℝ) (hroot : MvPolynomial.eval x0 q = 0)
    (H : Fin n → Polynomial (Polynomial ℤ)) (hH : ∀ i, H i ≠ 0)
    (hann : ∀ i, IsCoordinateAnnihilator q D i (H i))
    (B : ℕ) (hB : ∀ i, coefficientMass (H i).trailingCoeff ≤ B) :
    ∃ a : Fin n → ℝ, MvPolynomial.eval a q = 0 ∧ ∀ i, |a i| < (B : ℝ) + 1 := by
  obtain ⟨a, hq, _ha, _ht, hb⟩ := exists_root_with_annihilants q D x0 hroot H hH hann
  refine ⟨a, hq, ?_⟩
  intro i
  have hm : (coefficientMass (H i).trailingCoeff : ℝ) ≤ B := by exact_mod_cast hB i
  linarith [hb i]

/-- The same radius theorem directly accepts certificates in the actual
coercive gradient ideals. -/
theorem exists_root_bounded_of_ideal (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (x0 : Fin n → ℝ) (hroot : MvPolynomial.eval x0 q = 0)
    (H : Fin n → Polynomial (Polynomial ℤ)) (hH : ∀ i, H i ≠ 0)
    (hI : ∀ i s, 0 < s → coordinatePolynomial (H i) s i ∈
      CoerciveCriticalFibers.generated (fun j => MvPolynomial.pderiv j
        (CoerciveCriticalFibers.polynomial q D s)))
    (B : ℕ) (hB : ∀ i, coefficientMass (H i).trailingCoeff ≤ B) :
    ∃ a : Fin n → ℝ, MvPolynomial.eval a q = 0 ∧ ∀ i, |a i| < (B : ℝ) + 1 :=
  exists_root_bounded q D x0 hroot H hH
    (fun i => isCoordinateAnnihilator_of_ideal q D i (H i) (hI i)) B hB

end LeanCanny.Geometry.CoerciveAnnihilatorLimit

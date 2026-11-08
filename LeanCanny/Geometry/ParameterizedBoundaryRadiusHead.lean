/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.ParameterizedBoundaryGramMass
public import LeanCanny.Geometry.EffectiveRegularPolynomialLevels
public import LeanCanny.Geometry.PolynomialLimitAnnihilator
public import LeanCanny.Algebra.IntegerRootBound
/-! # An original-bounded integer head for finite boundary-radius limits

The parameter-lowest coefficient of the same fixed Gram slice is nonzero.
Its integer mass bounds every finite limit of actual critical squared norms
as the positive residual parameter tends to zero. Multipliers need not be
bounded. This is not yet a component-stabilization theorem.
-/
@[expose] public section
namespace LeanCanny.Geometry.ParameterizedBoundaryRadiusHead
open LeanCanny.Algebra MvPolynomial Filter Set
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def radiusExponent (n D b : ℕ) : ℕ := ParameterizedBoundaryGramMass.headBits n D b + 1

noncomputable def polynomial (q : MvPolynomial (Fin n) ℤ) (D : ℕ) : Polynomial ℤ :=
  (Polynomial.Bivariate.swap (ParameterizedBoundaryGramValues.head q D)).trailingCoeff

theorem ne_zero (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D) : polynomial q D ≠ 0 := by
  apply Polynomial.trailingCoeff_ne_zero.mpr
  intro H
  apply ParameterizedBoundaryGramValues.head_ne_zero q D hD
  have HE := congrArg Polynomial.Bivariate.swap H
  simpa only [Polynomial.Bivariate.swap_swap_apply,map_zero] using HE

theorem mass (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^b) :
    coefficientMass (polynomial q D) ≤ 2^ParameterizedBoundaryGramMass.headBits n D b := by
  apply (NestedMass.coeff_le (Polynomial.Bivariate.swap (ParameterizedBoundaryGramValues.head q D)) _).trans
  rw [NestedMass.swap]
  exact ParameterizedBoundaryGramMass.head_mass q D b hD hq

theorem exceptional_mass (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^b) :
    coefficientMass (ParameterizedBoundaryGramValues.exceptional q D) ≤
      2^ParameterizedBoundaryGramMass.headBits n D b := by
  have HE : ParameterizedBoundaryGramValues.exceptional q D =
      (ParameterizedBoundaryGramValues.head q D).leadingCoeff := rfl
  rw [HE,Polynomial.leadingCoeff]
  exact (NestedMass.coeff_le _ _).trans (ParameterizedBoundaryGramMass.head_mass q D b hD hq)

theorem root_bound (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^b) (a : ℝ)
    (ha : (polynomial q D).eval₂ (Int.castRingHom ℝ) a = 0) : |a| < 2^radiusExponent n D b := by
  have H := abs_root_lt_coefficientMass_add_one (polynomial q D) (ne_zero q D hD) a ha
  have HM : (coefficientMass (polynomial q D) : ℝ) ≤ 2^ParameterizedBoundaryGramMass.headBits n D b := by
    exact_mod_cast mass q D b hD hq
  have HP : (1 : ℝ) ≤ 2^ParameterizedBoundaryGramMass.headBits n D b := one_le_pow₀ (by norm_num)
  unfold radiusExponent
  rw [pow_succ]
  linarith

private theorem swap_value (Q : Polynomial (Polynomial ℤ)) (e t : ℝ) :
    PolynomialLimitAnnihilator.value (Polynomial.Bivariate.swap Q) e t =
      Q.eval₂ (ParameterizedBoundaryCriticalValues.parameter e) t := by
  simpa [PolynomialLimitAnnihilator.value,ParameterizedBoundaryCriticalValues.parameter,
    Polynomial.aevalAeval,Polynomial.aevalAevalEquiv,Polynomial.aeval_def,
    Polynomial.eval₂_hom,Polynomial.eval₂_eval₂RingHom_apply,Polynomial.evalEval,Polynomial.eval_map] using
      Polynomial.Bivariate.aevalAeval_swap t e Q

theorem critical_limit_root (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^b)
    (epsilon : ℕ → ℝ) (x : ℕ → Fin n → ℝ) (lambda : ℕ → ℝ) (a : ℝ)
    (hpos : ∀ k, 0 < epsilon k) (hzero : Tendsto epsilon atTop (𝓝 0))
    (hlim : Tendsto (fun k => ∑ i, x k i^2) atTop (𝓝 a))
    (he : ∀ᶠ k in atTop, (q.eval₂ (Int.castRingHom ℝ) (x k))^2 = epsilon k)
    (hx : ∀ᶠ k in atTop, ∀ i, 2*x k i + lambda k*(2*q.eval₂ (Int.castRingHom ℝ) (x k)*
      (pderiv i q).eval₂ (Int.castRingHom ℝ) (x k)) = 0) :
    (polynomial q D).eval₂ (Int.castRingHom ℝ) a = 0 := by
  let B := ParameterizedBoundaryGramMass.headBits n D b
  have HDelta : 0 < InfinitesimalSign.dyadic (B+1) := by unfold InfinitesimalSign.dyadic; positivity
  have HSmall : ∀ᶠ k in atTop, epsilon k ≤ InfinitesimalSign.dyadic (B+1) :=
    (hzero.eventually (Iio_mem_nhds HDelta)).mono (fun _ hk => hk.le)
  apply PolynomialLimitAnnihilator.trailingCoeff_eval_eq_zero_of_eventually
    (Polynomial.Bivariate.swap (ParameterizedBoundaryGramValues.head q D)) epsilon
    (fun k => ∑ i, x k i^2) a (fun k => ne_of_gt (hpos k)) hzero hlim
  filter_upwards [HSmall,he,hx] with k hk hke hkx
  rw [swap_value]
  apply ParameterizedBoundaryGramValues.eval_head q D hD (epsilon k) ?_ (x k) (lambda k) hke hkx
  exact InfinitesimalSign.eval_ne_zero_le_dyadic (ParameterizedBoundaryGramValues.exceptional q D) B
    (ParameterizedBoundaryGramValues.exceptional_ne_zero q D hD) (exceptional_mass q D b hD hq)
    (epsilon k) (hpos k) hk

end LeanCanny.Geometry.ParameterizedBoundaryRadiusHead

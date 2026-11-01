/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralParameterInverse
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Basic.Real.Basic

/-! # Integer-leading relative scalar polynomials without a degree increase

A possibly zero-divisor leading coefficient is inverted only after
specializing to a nonzero real value. Its integer multiplication-matrix
characteristic polynomial supplies a nonzero integer denominator. The
normalized polynomial has that integer top coefficient and the same
scalar degree and exactly the same specialized roots. No full integer
norm of the scalar polynomial is formed.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralRelativeLeadingNormalization
open Polynomial
open scoped Classical
variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]

noncomputable def denominator (b : Module.Basis ι ℤ A) (a : A) : ℤ :=
  IntegralParameterInverse.denominator (Algebra.leftMulMatrix b a).charpoly

noncomputable def inverseValue (b : Module.Basis ι ℤ A) (a : A) : A :=
  Polynomial.aeval a (IntegralParameterInverse.inverse (Algebra.leftMulMatrix b a).charpoly)

noncomputable def normalize (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) : Polynomial A :=
  monomial d (denominator b (p.coeff d) : A) +
    C (inverseValue b (p.coeff d)) * (p - monomial d (p.coeff d))

theorem denominator_ne_zero (b : Module.Basis ι ℤ A) (a : A) : denominator b a ≠ 0 :=
  IntegralParameterInverse.charpoly_denominator_ne_zero b a

theorem coefficient (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) :
    (normalize b p d).coeff d = (denominator b (p.coeff d) : A) := by
  simp only [normalize, coeff_add, coeff_monomial, ite_true, coeff_C_mul, coeff_sub, sub_self, mul_zero, add_zero]

theorem natDegree_le (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) (hd : p.natDegree ≤ d) :
    (normalize b p d).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have H : d ≠ k := by omega
  simp only [normalize, coeff_add, coeff_monomial, H, ite_false, coeff_C_mul, coeff_sub,
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt hk), sub_zero, mul_zero, add_zero]

theorem inverseValue_eval (b : Module.Basis ι ℤ A) (a : A) (φ : A →ₐ[ℤ] ℝ) :
    φ (inverseValue b a) =
      (IntegralParameterInverse.inverse (Algebra.leftMulMatrix b a).charpoly).eval₂ (Int.castRingHom ℝ) (φ a) := by
  change φ (Polynomial.aeval a _) = _
  rw [← Polynomial.aeval_algHom_apply]
  rfl

theorem mul_inverseValue (b : Module.Basis ι ℤ A) (a : A) (φ : A →ₐ[ℤ] ℝ) (ha : φ a ≠ 0) :
    φ a * φ (inverseValue b a) = (denominator b a : ℝ) := by
  rw [inverseValue_eval]
  exact IntegralParameterInverse.mul_inverse_eval _ (Int.castRingHom ℝ) (φ a) ha
    (IntegralParameterInverse.charpoly_root b a φ)

theorem inverseValue_ne_zero (b : Module.Basis ι ℤ A) (a : A) (φ : A →ₐ[ℤ] ℝ) (ha : φ a ≠ 0) :
    φ (inverseValue b a) ≠ 0 := by
  intro H
  have HE := mul_inverseValue b a φ ha
  rw [H, mul_zero] at HE
  exact Int.cast_ne_zero.mpr (denominator_ne_zero b a) HE.symm

theorem eval_eq (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ)
    (φ : A →ₐ[ℤ] ℝ) (ha : φ (p.coeff d) ≠ 0) (t : ℝ) :
    (normalize b p d).eval₂ φ.toRingHom t = φ (inverseValue b (p.coeff d)) * p.eval₂ φ.toRingHom t := by
  have H := mul_inverseValue b (p.coeff d) φ ha
  simp only [normalize, eval₂_add, eval₂_monomial, eval₂_mul, eval₂_C, eval₂_sub, map_intCast]
  change (denominator b (p.coeff d) : ℝ) * t ^ d +
    φ (inverseValue b (p.coeff d)) * (p.eval₂ φ.toRingHom t - φ (p.coeff d) * t ^ d) = _
  rw [← H]
  ring

theorem root_iff (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ)
    (φ : A →ₐ[ℤ] ℝ) (ha : φ (p.coeff d) ≠ 0) (t : ℝ) :
    (normalize b p d).eval₂ φ.toRingHom t = 0 ↔ p.eval₂ φ.toRingHom t = 0 := by
  rw [eval_eq b p d φ ha]
  exact mul_eq_zero.trans (or_iff_right (inverseValue_ne_zero b (p.coeff d) φ ha))

theorem specialized_degree (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ)
    (hd : p.natDegree ≤ d) (φ : A →ₐ[ℤ] ℝ) :
    ((normalize b p d).map φ.toRingHom).natDegree = d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero ((natDegree_map_le).trans (natDegree_le b p d hd))
  rw [coeff_map, coefficient, map_intCast]
  exact Int.cast_ne_zero.mpr (denominator_ne_zero b (p.coeff d))

end LeanCanny.Algebra.IntegralRelativeLeadingNormalization

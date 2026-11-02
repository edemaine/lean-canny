/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHistory
public import LeanCanny.Algebra.IntegerRootBound
public import LeanCanny.Algebra.IntegralParameterInverse
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
/-! # Real values of a bounded retained bank under its actual hom

The multiplication matrix supplies an integer characteristic polynomial for
its actual algebra element. A coefficient-mass root bound applies after the
chosen hom. Nonzero integer denominators have real absolute value at least1.
No new level coefficient or later source enters this bound.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRetainedRealBound
open Polynomial IntegralMixedHistory
open scoped Classical

def height (R G : ℕ) : ℕ := R.size+CharacteristicIntegerBounds.budget R G+1

theorem height_binary {R G : List Bool → ℕ} (hR : BinaryFn R) (hG : BinaryFn G) :
    BinaryFn (fun q => height (R q) (G q)) :=
  (hR.size.add (CharacteristicIntegerBounds.budget_binary hR hG)).add (BinaryFn.const 1)

theorem algebra_value {R G : ℕ} {A : Type*} [CommRing A]
    (b : Module.Basis (Fin R) ℤ A) (a : A)
    (H : ∀ r t, (Algebra.leftMulMatrix b a r t).natAbs ≤ 2^G) (φ : A →ₐ[ℤ] ℝ) :
    |φ a| ≤ (2:ℝ)^height R G := by
  let M := Algebra.leftMulMatrix b a
  have HC : ∀ k, (M.charpoly.coeff k).natAbs ≤ 2^CharacteristicIntegerBounds.budget R G := by
    intro k
    exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide)
      (CharacteristicIntegerBounds.coefficient_bits M G H k))
  have HM : coefficientMass M.charpoly ≤ 2^(R.size+CharacteristicIntegerBounds.budget R G) := by
    have HD : M.charpoly.natDegree ≤ R := by simp
    have HR : R+1 ≤ 2^R.size := by have H := Nat.lt_size_self R; omega
    exact (coefficientMass_le M.charpoly R _ HD HC).trans (by
      rw [pow_add]
      exact Nat.mul_le_mul_right _ HR)
  have HB := abs_root_lt_coefficientMass_add_one M.charpoly (Matrix.charpoly_monic M).ne_zero
    (φ a) (IntegralParameterInverse.charpoly_root b a φ)
  have HMR : (coefficientMass M.charpoly:ℝ) ≤ (2:ℝ)^(R.size+CharacteristicIntegerBounds.budget R G) := by
    exact_mod_cast HM
  have HP : 1 ≤ (2:ℝ)^(R.size+CharacteristicIntegerBounds.budget R G) := one_le_pow₀ (by norm_num)
  unfold height
  rw [pow_succ]
  linarith

theorem quotient {n S B m G : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (HG : x.bank.Bounds G)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (i : Fin m) :
    |φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)| ≤
      (2:ℝ)^height (FixedWidthPolynomial.count m B) G := by
  have HN := algebra_value x.sampler.scalarPrefix.basis.finBasis (x.bank.numerator i) (HG.numerator i) φ
  have HD : (1:ℝ) ≤ |(x.bank.denominator i:ℝ)| := by
    have HZ : (1:ℤ) ≤ |x.bank.denominator i| := by
      have HP := abs_pos.mpr (x.denominator_ne_zero i)
      omega
    exact_mod_cast HZ
  rw [abs_div]
  exact (div_le_self (abs_nonneg _) HD).trans HN

end LeanCanny.Algebra.IntegralMixedRetainedRealBound

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MvCoefficientChainRule
public import LeanCanny.Algebra.ProjectionCoordinateAlgebraic

/-! # Critical-coordinate algebraicity while holding parameters fixed

A direction derivation need not fix the whole coefficient field. It suffices
that its coefficientwise action fixes every constraint polynomial. Extending
it to the critical-point field differentiates the algebraic projection value
into a point coordinate. Symbolic level parameters can therefore remain fixed.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionParameterAlgebraic
open MvPolynomial
open scoped BigOperators

variable {K B L ι σ : Type*} [Field K] [Field B] [Field L]
  [Algebra K B] [Algebra K L] [Algebra B L] [IsScalarTower K B L]
  [Fintype ι] [Fintype σ]

omit [IsScalarTower K B L] in
theorem tangent_sum_zero (D : Derivation K B B) (δ : Derivation K L L)
    (hD : ∀ b : B, δ (algebraMap B L b) = algebraMap B L (D b))
    (f : σ → MvPolynomial ι B) (x w : ι → L) (lambda : σ → L)
    (hfixed : ∀ a, MvCoefficientDerivation.derivation D (f a) = 0)
    (hf : ∀ a, aeval x (f a) = 0)
    (hw : ∀ i, w i = ∑ a, lambda a * aeval x (pderiv i (f a))) :
    ∑ i, w i * δ (x i) = 0 := by
  calc
    _ = ∑ i, ∑ a, lambda a * (aeval x (pderiv i (f a)) * δ (x i)) := by
      simp only [hw, Finset.sum_mul, mul_assoc]
    _ = ∑ a, lambda a * ∑ i, aeval x (pderiv i (f a)) * δ (x i) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      rw [← MvCoefficientChainRule.chain_rule_of_fixed D δ hD (f a) x (hfixed a), hf, map_zero, mul_zero]

omit [IsScalarTower K B L] in
theorem linearValue_derivative (D : Derivation K B B) (δ : Derivation K L L)
    (hD : ∀ b : B, δ (algebraMap B L b) = algebraMap B L (D b))
    (f : σ → MvPolynomial ι B) (x : ι → L) (v : ι → B) (lambda : σ → L)
    (hfixed : ∀ a, MvCoefficientDerivation.derivation D (f a) = 0)
    (hf : ∀ a, aeval x (f a) = 0)
    (hv : ∀ i, algebraMap B L (v i) = ∑ a, lambda a * aeval x (pderiv i (f a))) :
    δ (ProjectionCoordinateAlgebraic.linearValue v x) = ∑ i, δ (algebraMap B L (v i)) * x i := by
  simp only [ProjectionCoordinateAlgebraic.linearValue, map_sum, δ.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  rw [tangent_sum_zero D δ hD f x (fun i => algebraMap B L (v i)) lambda hfixed hf hv, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem algebraic_coordinate [CharZero B] [DecidableEq ι]
    (f : σ → MvPolynomial ι B) (x : ι → L) (v : ι → B) (lambda : σ → L)
    (hf : ∀ a, aeval x (f a) = 0)
    (hv : ∀ i, algebraMap B L (v i) = ∑ a, lambda a * aeval x (pderiv i (f a)))
    (j : ι) (D : Derivation K B B)
    (hfixed : ∀ a, MvCoefficientDerivation.derivation D (f a) = 0)
    (hcoord : ∀ i, D (v i) = if i = j then 1 else 0) : IsAlgebraic B (x j) := by
  obtain ⟨δ, hδ⟩ := FieldDerivationExtension.exists_extension (L := L) D
  have hvalue := ProjectionCoordinateAlgebraic.algebraic_value (K := B) f x v lambda hf hv
  have ha := AlgebraicDerivative.algebraic_derivative D δ hδ hvalue
  have he : δ (ProjectionCoordinateAlgebraic.linearValue v x) = x j := by
    rw [linearValue_derivative D δ hδ f x v lambda hfixed hf hv]
    simp [hδ, hcoord]
  exact he ▸ ha

theorem algebraic_normalized_coordinates [CharZero B] [DecidableEq ι]
    (f : σ → MvPolynomial ι B) (x : ι → L) (v : ι → B) (lambda : σ → L)
    (hf : ∀ a, aeval x (f a) = 0)
    (hv : ∀ i, algebraMap B L (v i) = ∑ a, lambda a * aeval x (pderiv i (f a)))
    (base : ι) (hbase : v base = 1)
    (D : {i : ι // i ≠ base} → Derivation K B B)
    (hfixed : ∀ j a, MvCoefficientDerivation.derivation (D j) (f a) = 0)
    (hcoord : ∀ j i, D j (v i) = if i = j.val then 1 else 0) : ∀ i, IsAlgebraic B (x i) := by
  classical
  have hother (j : {i : ι // i ≠ base}) : IsAlgebraic B (x j) :=
    algebraic_coordinate f x v lambda hf hv j (D j) (hfixed j) (hcoord j)
  let s := Finset.univ.erase base
  have hsum : IsAlgebraic B (∑ i ∈ s, algebraMap B L (v i) * x i) :=
    ProjectionCoordinateAlgebraic.algebraic_finset_sum s _ (fun i hi =>
      (isAlgebraic_algebraMap (v i)).mul (hother ⟨i, (Finset.mem_erase.mp hi).1⟩))
  have hid : ProjectionCoordinateAlgebraic.linearValue v x =
      x base + ∑ i ∈ s, algebraMap B L (v i) * x i := by
    rw [ProjectionCoordinateAlgebraic.linearValue, ← Finset.add_sum_erase _ _ (Finset.mem_univ base),
      hbase, map_one, one_mul]
  have hb : IsAlgebraic B (x base) := by
    have h := (ProjectionCoordinateAlgebraic.algebraic_value (K := B) f x v lambda hf hv).sub hsum
    rw [hid, add_sub_cancel_right] at h
    exact h
  intro i
  by_cases hi : i = base
  · simpa only [hi] using hb
  · exact hother ⟨i, hi⟩

end LeanCanny.Algebra.ProjectionParameterAlgebraic

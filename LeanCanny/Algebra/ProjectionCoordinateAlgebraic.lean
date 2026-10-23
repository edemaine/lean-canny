/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FieldDerivationExtension
public import LeanCanny.Algebra.CoordinateDerivation
public import LeanCanny.Algebra.AlgebraicDerivative
public import LeanCanny.Algebra.CriticalValueAlgebraic
import Mathlib.Tactic.Ring

/-! # Algebraicity of critical coordinates for generic linear projections

Normalized stationarity kills the tangent term in differentiation of the
projection value. The value is algebraic over the direction field. Extending
coordinate derivations of that field differentiates the value into the point
coordinates, which are consequently algebraic as well.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionCoordinateAlgebraic
open MvPolynomial
open scoped BigOperators

variable {K L ι σ : Type*} [Field K] [Field L] [Algebra K L] [Fintype ι] [Fintype σ]

theorem tangent_sum_zero (δ : Derivation K L L) (f : σ → MvPolynomial ι K)
    (x w : ι → L) (lambda : σ → L) (hf : ∀ a, aeval x (f a) = 0)
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
      rw [← CriticalValueAlgebraic.chain_rule, hf, map_zero, mul_zero]

variable {B : Type*} [Field B] [Algebra K B] [Algebra B L] [IsScalarTower K B L]

noncomputable def linearValue (v : ι → B) (x : ι → L) : L := ∑ i, algebraMap B L (v i) * x i

omit [Algebra K B] [IsScalarTower K B L] in
theorem linearValue_derivative (δ : Derivation K L L) (f : σ → MvPolynomial ι K)
    (x : ι → L) (v : ι → B) (lambda : σ → L) (hf : ∀ a, aeval x (f a) = 0)
    (hv : ∀ i, algebraMap B L (v i) = ∑ a, lambda a * aeval x (pderiv i (f a))) :
    δ (linearValue v x) = ∑ i, δ (algebraMap B L (v i)) * x i := by
  simp only [linearValue, map_sum, δ.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  rw [tangent_sum_zero δ f x (fun i => algebraMap B L (v i)) lambda hf hv, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem algebraic_value [CharZero B] (f : σ → MvPolynomial ι K)
    (x : ι → L) (v : ι → B) (lambda : σ → L) (hf : ∀ a, aeval x (f a) = 0)
    (hv : ∀ i, algebraMap B L (v i) = ∑ a, lambda a * aeval x (pderiv i (f a))) :
    IsAlgebraic B (linearValue v x) := by
  apply TranscendentalDerivation.algebraic_of_all_derivations_vanish
  intro δ
  have h := linearValue_derivative (δ.restrictScalars K) f x v lambda hf hv
  simpa only [Derivation.restrictScalars_apply, Derivation.map_algebraMap, zero_mul, Finset.sum_const_zero] using h

theorem algebraic_coordinate_of_derivation [CharZero B] [DecidableEq ι]
    (f : σ → MvPolynomial ι K) (x : ι → L) (v : ι → B) (lambda : σ → L)
    (hf : ∀ a, aeval x (f a) = 0)
    (hv : ∀ i, algebraMap B L (v i) = ∑ a, lambda a * aeval x (pderiv i (f a)))
    (j : ι) (D : Derivation K B B) (hD : ∀ i, D (v i) = if i = j then 1 else 0) :
    IsAlgebraic B (x j) := by
  obtain ⟨δ, hδ⟩ := FieldDerivationExtension.exists_extension (L := L) D
  have ha := AlgebraicDerivative.algebraic_derivative D δ hδ (algebraic_value f x v lambda hf hv)
  have he : δ (linearValue v x) = x j := by
    rw [linearValue_derivative δ f x v lambda hf hv]
    simp [hδ, hD]
  exact he ▸ ha

theorem algebraic_coordinates [CharZero K] (f : σ → MvPolynomial ι K)
    (x : ι → L) (v : ι → B) (lambda : σ → L) (hf : ∀ a, aeval x (f a) = 0)
    (hv : ∀ i, algebraMap B L (v i) = ∑ a, lambda a * aeval x (pderiv i (f a)))
    (hind : AlgebraicIndependent K v) : ∀ i, IsAlgebraic B (x i) := by
  classical
  let : CharZero B := charZero_of_injective_algebraMap (algebraMap K B).injective
  intro i
  obtain ⟨D, hD⟩ := CoordinateDerivation.exists_of_independent hind i
  exact algebraic_coordinate_of_derivation f x v lambda hf hv i D hD

theorem algebraic_finset_sum {τ : Type*} (s : Finset τ) (g : τ → L)
    (hg : ∀ i ∈ s, IsAlgebraic B (g i)) : IsAlgebraic B (∑ i ∈ s, g i) := by
  exact (IsIntegral.sum g (fun i hi => (hg i hi).isIntegral)).isAlgebraic

theorem algebraic_normalized_coordinates [CharZero K] (f : σ → MvPolynomial ι K)
    (x : ι → L) (v : ι → B) (lambda : σ → L) (hf : ∀ a, aeval x (f a) = 0)
    (hv : ∀ i, algebraMap B L (v i) = ∑ a, lambda a * aeval x (pderiv i (f a)))
    (base : ι) (hbase : v base = 1)
    (hind : AlgebraicIndependent K (fun i : {i : ι // i ≠ base} => v i)) :
    ∀ i, IsAlgebraic B (x i) := by
  classical
  let : CharZero B := charZero_of_injective_algebraMap (algebraMap K B).injective
  have hother (j : {i : ι // i ≠ base}) : IsAlgebraic B (x j) := by
    obtain ⟨D, hD⟩ := CoordinateDerivation.exists_of_independent hind j
    have hcoord : ∀ i, D (v i) = if i = j.val then 1 else 0 := by
      intro i
      by_cases hi : i = base
      · subst i
        simp only [hbase, D.map_one_eq_zero, Ne.symm j.property, ↓reduceIte]
      · simpa only [Subtype.ext_iff] using hD ⟨i, hi⟩
    exact algebraic_coordinate_of_derivation f x v lambda hf hv j D hcoord
  let s := Finset.univ.erase base
  have hsum : IsAlgebraic B (∑ i ∈ s, algebraMap B L (v i) * x i) :=
    algebraic_finset_sum s _ (fun i hi =>
      (isAlgebraic_algebraMap (v i)).mul (hother ⟨i, (Finset.mem_erase.mp hi).1⟩))
  have hid : linearValue v x = x base + ∑ i ∈ s, algebraMap B L (v i) * x i := by
    rw [linearValue, ← Finset.add_sum_erase _ _ (Finset.mem_univ base), hbase, map_one, one_mul]
  have hb : IsAlgebraic B (x base) := by
    have h := (algebraic_value f x v lambda hf hv).sub hsum
    rw [hid, add_sub_cancel_right] at h
    exact h
  intro i
  by_cases hi : i = base
  · simpa only [hi] using hb
  · exact hother ⟨i, hi⟩

end LeanCanny.Algebra.ProjectionCoordinateAlgebraic

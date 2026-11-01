/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedHistoryScript

/-! # Frozen-level semantics of mixed critical commands

Common-denominator expressions evaluate to the intended affine levels
for every interpreting hom satisfying the explicit retained-value guards.
Invalid references have the stated zero semantics. No independence of
scalar roots is confused with correlation to a selected physical sample.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
open LeanCanny.Encoding LeanCanny.Computation IntegralHistorySampler UniformIntegralPrefix
open scoped Classical

def AffineExpr.evaluate {m : ℕ} (values : Fin m → ℝ) : AffineExpr → ℝ
  | .constant c => c
  | .reference j => if hj : j < m then values ⟨j, hj⟩ else 0
  | .add a b => a.evaluate values + b.evaluate values
  | .scale c a => (c : ℝ) * a.evaluate values

theorem cleared_recover {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (values : Fin m → ℝ)
    (H : ∀ i, φ (x.bank.numerator i) / (x.bank.denominator i : ℝ) = values i) (i : Fin m) :
    φ (cleared x i) = (commonDenominator x : ℝ) * values i := by
  have HE := (CommonIntegerDenominator.recover φ.toRingHom Finset.univ x.bank.denominator x.bank.numerator
    (fun j _ => x.denominator_ne_zero j) i (Finset.mem_univ i)).trans (H i)
  have HZ : (commonDenominator x : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)
  exact (div_eq_iff HZ).mp HE |>.trans (mul_comm _ _)

theorem expression_recover {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (values : Fin m → ℝ)
    (H : ∀ i, φ (x.bank.numerator i) / (x.bank.denominator i : ℝ) = values i) (a : AffineExpr) :
    φ (expression x a) = (commonDenominator x : ℝ) * a.evaluate values := by
  induction a with
  | constant c => simp only [expression, AffineExpr.evaluate, map_mul, map_intCast]
  | reference j =>
    simp only [expression, AffineExpr.evaluate]
    by_cases hj : j < m
    · simp only [hj, dite_true]
      exact cleared_recover x φ values H ⟨j, hj⟩
    · simp only [hj, dite_false, map_zero, mul_zero]
  | add a b ha hb =>
    simp only [expression, AffineExpr.evaluate, map_add, ha, hb]
    ring
  | scale c a ha =>
    simp only [expression, AffineExpr.evaluate, map_mul, map_intCast, ha]
    ring

end LeanCanny.Algebra.IntegralMixedHistory

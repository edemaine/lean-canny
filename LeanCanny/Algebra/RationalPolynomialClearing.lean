/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteDenominatorClearing
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Explicit integer normalization of bounded-degree polynomial families

A common product of coefficient denominators clears an entire rational
polynomial family. The coefficient formula is a numerator times all other
denominators, suitable for modular streaming without inverses. Degrees are
preserved and the coefficient bit budget is explicit.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalPolynomialClearing
open Polynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def entries (p : σ → ℚ[X]) (D : ℕ) : σ × Fin (D + 1) → ℚ := fun a => (p a.1).coeff a.2.val

def scale (p : σ → ℚ[X]) (D : ℕ) : ℕ := FiniteDenominatorClearing.scale (entries p D)

def polynomial (p : σ → ℚ[X]) (D : ℕ) (s : σ) : ℤ[X] :=
  Polynomial.ofFn (D + 1) (fun k => FiniteDenominatorClearing.cleared (entries p D) (s, k))

omit [DecidableEq σ] in
theorem scale_pos (p : σ → ℚ[X]) (D : ℕ) : 0 < scale p D :=
  FiniteDenominatorClearing.scale_pos _

theorem coeff_lt (p : σ → ℚ[X]) (D : ℕ) (s : σ) (k : ℕ) (hk : k < D + 1) :
    (polynomial p D s).coeff k = FiniteDenominatorClearing.cleared (entries p D) (s, ⟨k, hk⟩) :=
  Polynomial.ofFn_coeff_eq_val_of_lt _ hk

theorem coeff_ge (p : σ → ℚ[X]) (D : ℕ) (s : σ) (k : ℕ) (hk : D + 1 ≤ k) :
    (polynomial p D s).coeff k = 0 := Polynomial.ofFn_coeff_eq_zero_of_ge _ hk

theorem map_polynomial (p : σ → ℚ[X]) (D : ℕ) (hp : ∀ s, (p s).natDegree ≤ D) (s : σ) :
    (polynomial p D s).map (algebraMap ℤ ℚ) = C (scale p D : ℚ) * p s := by
  ext k
  rw [Polynomial.coeff_map, Polynomial.coeff_C_mul]
  by_cases hk : k < D + 1
  · rw [coeff_lt p D s k hk]
    exact FiniteDenominatorClearing.cast_cleared (entries p D) (s, ⟨k, hk⟩)
  · rw [coeff_ge p D s k (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (show (p s).natDegree < k by
      have h := hp s
      omega)]
    simp

theorem natDegree_polynomial (p : σ → ℚ[X]) (D : ℕ) (hp : ∀ s, (p s).natDegree ≤ D) (s : σ) :
    (polynomial p D s).natDegree = (p s).natDegree := by
  have hi : Function.Injective (algebraMap ℤ ℚ) := Int.cast_injective
  rw [← Polynomial.natDegree_map_eq_of_injective hi, map_polynomial p D hp s,
    Polynomial.natDegree_C_mul (Nat.cast_ne_zero.mpr (scale_pos p D).ne')]

theorem coeff_size_le (p : σ → ℚ[X]) (D B : ℕ)
    (hp : ∀ s k, k ≤ D → ((p s).coeff k).num.natAbs.size ≤ B ∧ ((p s).coeff k).den.size ≤ B)
    (s : σ) (k : ℕ) : ((polynomial p D s).coeff k).natAbs.size ≤ B * (Fintype.card σ * (D + 1)) + 1 := by
  by_cases hk : k < D + 1
  · rw [coeff_lt p D s k hk]
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      FiniteDenominatorClearing.cleared_size_le (entries p D) B
        (fun a => hp a.1 a.2.val (by have h := a.2.isLt; omega)) (s, ⟨k, hk⟩)
  · rw [coeff_ge p D s k (by omega)]
    simp

omit [DecidableEq σ] in
theorem scale_size_le (p : σ → ℚ[X]) (D B : ℕ)
    (hp : ∀ s k, k ≤ D → ((p s).coeff k).den.size ≤ B) :
    (scale p D).size ≤ B * (Fintype.card σ * (D + 1)) + 1 := by
  simpa only [scale, Fintype.card_prod, Fintype.card_fin] using
    FiniteDenominatorClearing.scale_size_le (entries p D) B
      (fun a => hp a.1 a.2.val (by have h := a.2.isLt; omega))

end LeanCanny.Algebra.RationalPolynomialClearing

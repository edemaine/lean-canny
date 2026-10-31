/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
import Lean.Elab.Tactic.Omega

/-! # Bounded matrix powers normalize degree-decreasing reductions

Normal states are absorbing. Every other nonzero transition decreases a
natural degree. After K+1 steps all columns are supported on normal states
when initial degrees are bounded by K. Matrix powering avoids a reduction
stack of depth K when K is a binary, potentially exponential, value.
-/

@[expose] public section
namespace LeanCanny.Algebra.GradedReductionMatrix
open Matrix
open scoped Classical BigOperators

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]

theorem nonnormal_pow_zero (T : Matrix ι ι R) (normal : ι → Prop) (degree : ι → ℕ)
    (ha : ∀ j, normal j → ∀ i, T i j = if i = j then 1 else 0)
    (hd : ∀ i j, ¬normal j → T i j ≠ 0 → degree i < degree j)
    (e : ℕ) (i j : ι) (hi : ¬normal i) (hij : degree j < e + degree i) :
    (T ^ e) i j = 0 := by
  induction e generalizing i j with
  | zero =>
    have hne : i ≠ j := by intro h; subst j; omega
    simp only [pow_zero, Matrix.one_apply, ite_eq_right hne]
  | succ e ih =>
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : normal k
    · have hne : i ≠ k := by rintro rfl; exact hi hk
      rw [ha k hk i, ite_eq_right hne, zero_mul]
    · by_cases hT : T i k = 0
      · rw [hT, zero_mul]
      · have hdeg := hd i k hk hT
        rw [ih k j hk (by omega), mul_zero]

theorem terminal_rows (T : Matrix ι ι R) (normal : ι → Prop) (degree : ι → ℕ)
    (ha : ∀ j, normal j → ∀ i, T i j = if i = j then 1 else 0)
    (hd : ∀ i j, ¬normal j → T i j ≠ 0 → degree i < degree j)
    (K : ℕ) (hK : ∀ j, degree j ≤ K) (i j : ι) (hi : ¬normal i) :
    (T ^ (K + 1)) i j = 0 :=
  nonnormal_pow_zero T normal degree ha hd _ i j hi (by have := hK j; omega)

theorem vecMul_pow (T : Matrix ι ι R) (v : ι → R) (hv : v ᵥ* T = v) (e : ℕ) :
    v ᵥ* T ^ e = v := by
  induction e with
  | zero => simp only [pow_zero, Matrix.vecMul_one]
  | succ e ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hv]

theorem normal_span (T : Matrix ι ι R) (normal : ι → Prop) (degree : ι → ℕ)
    (ha : ∀ j, normal j → ∀ i, T i j = if i = j then 1 else 0)
    (hd : ∀ i j, ¬normal j → T i j ≠ 0 → degree i < degree j)
    (K : ℕ) (hK : ∀ j, degree j ≤ K) (v : ι → R) (hv : v ᵥ* T = v) (j : ι) :
    v j = ∑ i ∈ Finset.univ.filter normal, v i * (T ^ (K + 1)) i j := by
  have H := congrFun (vecMul_pow T v hv (K + 1)) j
  calc
    _ = ∑ i, v i * (T ^ (K + 1)) i j := H.symm
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : normal i
      · rw [ite_eq_left hi]
      · rw [ite_eq_right hi, terminal_rows T normal degree ha hd K hK i j hi, mul_zero]

end LeanCanny.Algebra.GradedReductionMatrix

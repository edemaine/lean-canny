/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.Parity

/-! # Alternating products of adjacent factors

If `a₀=b₀` and `a_(k+1)=b_(k+1)*b_k`, the even and odd products of `a`
differ only by the final `b` factor. When that factor is one, the products
are equal. This uses no cancellation and holds in every commutative monoid.
-/

@[expose] public section

namespace LeanCanny.Algebra.AlternatingProducts
open scoped BigOperators Classical
variable {M : Type*} [CommMonoid M]

noncomputable def evenProduct (a : ℕ → M) (N : ℕ) : M :=
  ∏ k ∈ Finset.range N, if Even k then a k else 1

noncomputable def oddProduct (a : ℕ → M) (N : ℕ) : M :=
  ∏ k ∈ Finset.range N, if Even k then 1 else a k

theorem evenProduct_succ (a : ℕ → M) (N : ℕ) :
    evenProduct a (N + 1) = evenProduct a N * (if Even N then a N else 1) :=
  Finset.prod_range_succ _ _

theorem oddProduct_succ (a : ℕ → M) (N : ℕ) :
    oddProduct a (N + 1) = oddProduct a N * (if Even N then 1 else a N) :=
  Finset.prod_range_succ _ _

theorem adjacent_prefix (a b : ℕ → M) (hfirst : a 0 = b 0)
    (hnext : ∀ k, a (k + 1) = b (k + 1) * b k) (N : ℕ) :
    if Even N then evenProduct a (N + 1) = b N * oddProduct a (N + 1)
      else evenProduct a (N + 1) * b N = oddProduct a (N + 1) := by
  induction N with
  | zero => simpa [evenProduct, oddProduct] using hfirst
  | succ N ih =>
    by_cases hN : Even N
    · have hi : evenProduct a (N + 1) = b N * oddProduct a (N + 1) := by simpa [hN] using ih
      simp only [Nat.even_add_one, hN, not_true_eq_false, ite_false]
      rw [evenProduct_succ a (N + 1), oddProduct_succ a (N + 1)]
      simp only [Nat.even_add_one, hN, not_true_eq_false, ite_false, mul_one, hnext]
      rw [hi]
      ac_rfl
    · have hi : evenProduct a (N + 1) * b N = oddProduct a (N + 1) := by simpa [hN] using ih
      simp only [Nat.even_add_one, hN, not_false_eq_true, ite_true]
      rw [evenProduct_succ a (N + 1), oddProduct_succ a (N + 1)]
      simp only [Nat.even_add_one, hN, not_false_eq_true, ite_true, mul_one, hnext]
      calc
        _ = b (N + 1) * (evenProduct a (N + 1) * b N) := by ac_rfl
        _ = _ := congrArg (b (N + 1) * ·) hi

theorem even_eq_odd_of_adjacent (a b : ℕ → M) (hfirst : a 0 = b 0)
    (hnext : ∀ k, a (k + 1) = b (k + 1) * b k) (N : ℕ) (hlast : b N = 1) :
    evenProduct a (N + 1) = oddProduct a (N + 1) := by
  have hi := adjacent_prefix a b hfirst hnext N
  by_cases hN : Even N <;> simpa [hN, hlast] using hi

theorem evenProduct_mul (a b : ℕ → M) (N : ℕ) :
    evenProduct (fun k => a k * b k) N = evenProduct a N * evenProduct b N := by
  unfold evenProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  by_cases hk : Even k <;> simp [hk]

theorem oddProduct_mul (a b : ℕ → M) (N : ℕ) :
    oddProduct (fun k => a k * b k) N = oddProduct a N * oddProduct b N := by
  unfold oddProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  by_cases hk : Even k <;> simp [hk]

theorem evenProduct_one (N : ℕ) : evenProduct (fun _ => (1 : M)) N = 1 := by
  simp [evenProduct]

theorem oddProduct_one (N : ℕ) : oddProduct (fun _ => (1 : M)) N = 1 := by
  simp [oddProduct]

section Field
variable {K : Type*} [Field K]

noncomputable def ratio (a : ℕ → K) (N : ℕ) : K := evenProduct a N / oddProduct a N

theorem ratio_mul (a b : ℕ → K) (N : ℕ) :
    ratio (fun k => a k * b k) N = ratio a N * ratio b N := by
  rw [ratio, evenProduct_mul, oddProduct_mul, mul_div_mul_comm]
  rfl

theorem ratio_one (N : ℕ) : ratio (fun _ => (1 : K)) N = 1 := by
  rw [ratio, evenProduct_one, oddProduct_one, div_one]

theorem oddProduct_ne_zero (a : ℕ → K) (N : ℕ) (ha : ∀ k, a k ≠ 0) : oddProduct a N ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  by_cases hk : Even k
  · simp only [ite_eq_left hk, ne_eq, one_ne_zero, not_false_eq_true]
  · exact (ite_eq_right hk).trans_ne (ha k)

end Field

end LeanCanny.Algebra.AlternatingProducts

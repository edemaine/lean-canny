/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Indexed factors for rational-coordinate monomials

A block of width `W` contains `eᵢ` numerator factors followed by `W-eᵢ`
denominator factors. Division and remainder decode a flat factor address.
The product is exactly the cleared monomial, including zero-width blocks and
empty variable families. No exponent vector or factor list must be stored.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution
open scoped BigOperators

variable {R : Type*} [CommMonoid R]

def flatFactor (n d : ℕ → R) (e : ℕ → ℕ) (W j : ℕ) : R :=
  if j % W < e (j / W) then n (j / W) else d (j / W)

theorem prod_choice (n d : R) (e W : ℕ) (he : e ≤ W) :
    (∏ j ∈ Finset.range W, if j < e then n else d) = n ^ e * d ^ (W - e) := by
  have hp := Finset.prod_range_add (fun j => if j < e then n else d) e (W - e)
  rw [Nat.add_sub_of_le he] at hp
  rw [hp]
  have hl : (∏ j ∈ Finset.range e, if j < e then n else d) = n ^ e := by
    calc
      _ = ∏ _j ∈ Finset.range e, n := Finset.prod_congr rfl (fun j hj => ite_eq_left (Finset.mem_range.mp hj))
      _ = _ := by simp
  have hr : (∏ j ∈ Finset.range (W - e), if e + j < e then n else d) = d ^ (W - e) := by
    have h (j : ℕ) : ¬ e + j < e := by omega
    simp only [h, ↓reduceIte, Finset.prod_const, Finset.card_range]
  rw [hl, hr]

omit [CommMonoid R] in
theorem flatFactor_block (n d : ℕ → R) (e : ℕ → ℕ) (W i j : ℕ) (hW : 0 < W) (hj : j < W) :
    flatFactor n d e W (i * W + j) = if j < e i then n i else d i := by
  have hdiv : (i * W + j) / W = i := by
    rw [Nat.mul_comm i W, Nat.add_comm (W * i) j, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (i * W + j) % W = j := by
    rw [Nat.mul_comm i W, Nat.add_comm (W * i) j, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [flatFactor, hdiv, hmod]

theorem prod_flatFactor (n d : ℕ → R) (e : ℕ → ℕ) (A W : ℕ) (he : ∀ i, i < A → e i ≤ W) :
    (∏ j ∈ Finset.range (A * W), flatFactor n d e W j) =
      ∏ i ∈ Finset.range A, n i ^ e i * d i ^ (W - e i) := by
  by_cases hW : W = 0
  · subst W
    simp only [Nat.mul_zero, Finset.range_zero, Finset.prod_empty]
    symm
    apply Finset.prod_eq_one
    intro i hi
    have hzero : e i = 0 := by have := he i (Finset.mem_range.mp hi); omega
    simp only [hzero, Nat.sub_self, pow_zero, one_mul]
  · have hpos : 0 < W := by omega
    induction A with
    | zero => simp
    | succ A ih =>
      rw [Nat.succ_mul, Finset.prod_range_add, ih (fun i hi => he i (by omega)), Finset.prod_range_succ]
      have hb : (∏ j ∈ Finset.range W, flatFactor n d e W (A * W + j)) =
          ∏ j ∈ Finset.range W, if j < e A then n A else d A :=
        Finset.prod_congr rfl (fun j hj => flatFactor_block n d e W A j hpos (Finset.mem_range.mp hj))
      rw [hb, prod_choice _ _ _ _ (he A (by omega))]

end LeanCanny.Algebra.RationalSubstitution

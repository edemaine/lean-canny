/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! # A shared integer denominator for frozen rational heights

The product of the nonzero coordinate scalars is a common denominator.
Each numerator is multiplied by the product omitting its own scalar. These
integer factors preserve every retained polynomial parameter degree.
-/

@[expose] public section
namespace LeanCanny.Algebra.CommonIntegerDenominator
open scoped Classical BigOperators
variable {σ R : Type*} [DecidableEq σ] [CommRing R]

def denominator (s : Finset σ) (c : σ → ℤ) : ℤ := ∏ i ∈ s, c i

def numerator (s : Finset σ) (c : σ → ℤ) (H : σ → R) (i : σ) : R :=
  H i * (denominator (s.erase i) c : R)

omit [DecidableEq σ] in
theorem denominator_ne_zero (s : Finset σ) (c : σ → ℤ) (hc : ∀ i ∈ s, c i ≠ 0) : denominator s c ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr hc

theorem denominator_split (s : Finset σ) (c : σ → ℤ) (i : σ) (hi : i ∈ s) :
    denominator s c = c i * denominator (s.erase i) c :=
  (Finset.mul_prod_erase s c hi).symm

theorem recover {K : Type*} [Field K] [CharZero K] (φ : R →+* K) (s : Finset σ) (c : σ → ℤ)
    (H : σ → R) (hc : ∀ i ∈ s, c i ≠ 0) (i : σ) (hi : i ∈ s) :
    φ (numerator s c H i) / (denominator s c : K) = φ (H i) / (c i : K) := by
  have HE : (denominator (s.erase i) c : K) ≠ 0 := Int.cast_ne_zero.mpr
    (denominator_ne_zero _ c (fun j hj => hc j (Finset.mem_of_mem_erase hj)))
  rw [numerator, map_mul, map_intCast, denominator_split s c i hi, Int.cast_mul]
  exact mul_div_mul_right _ _ HE

omit [DecidableEq σ] in
theorem denominator_abs_bound (s : Finset σ) (c : σ → ℤ) (U : ℕ) (hc : ∀ i ∈ s, (c i).natAbs ≤ U) :
    (denominator s c).natAbs ≤ U ^ s.card := by
  change Int.natAbsHom (∏ i ∈ s, c i) ≤ _
  rw [map_prod]
  exact (Finset.prod_le_prod hc).trans_eq (by simp)

theorem numerator_degree {A : Type*} [CommRing A] (s : Finset σ) (c : σ → ℤ)
    (H : σ → Polynomial A) (i : σ) : (numerator s c H i).natDegree ≤ (H i).natDegree := by
  unfold numerator
  exact Polynomial.natDegree_mul_le.trans (by simp)

end LeanCanny.Algebra.CommonIntegerDenominator

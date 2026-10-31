/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CommonIntegerDenominator
public import LeanCanny.Algebra.IntegralActionHeightBounds
public import LeanCanny.Algebra.UniformIntegralPrefixLift

/-! # Heights after common-denominator clearing and later scalar embeddings

Clearing multiplies an actual retained numerator by integers only. Its
matrix bound grows with the number of denominators, without an old-rank
factor. Later scalar embeddings preserve the old matrix-entry bound.
-/

@[expose] public section
namespace LeanCanny.Algebra.CommonIntegerDenominator
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {σ A : Type*} [DecidableEq σ] [CommRing A] {M : ℕ}

omit [DecidableEq σ] in
theorem denominator_height (s : Finset σ) (c : σ → ℤ) (G : ℕ)
    (hc : ∀ i ∈ s, (c i).natAbs ≤ 2 ^ G) :
    (denominator s c).natAbs ≤ 2 ^ (s.card * G) := by
  exact (denominator_abs_bound s c (2 ^ G) hc).trans_eq (by rw [← pow_mul]; congr 1; exact Nat.mul_comm _ _)

theorem numerator_height (b : Module.Basis (Fin M) ℤ A) (s : Finset σ) (c : σ → ℤ)
    (H : σ → A) (V G : ℕ) (hc : ∀ i ∈ s, (c i).natAbs ≤ 2 ^ G)
    (i : σ) (hH : ∀ r t, (Algebra.leftMulMatrix b (H i) r t).natAbs ≤ 2 ^ V) (r t : Fin M) :
    (Algebra.leftMulMatrix b (numerator s c H i) r t).natAbs ≤ 2 ^ (V + s.card * G) := by
  have HD := denominator_height (s.erase i) c G (fun j hj => hc j (Finset.mem_of_mem_erase hj))
  unfold numerator
  rw [mul_comm, IntegralActionHeightBounds.int_multiply_entry, Int.natAbs_mul]
  calc
    _ ≤ 2 ^ ((s.erase i).card * G) * 2 ^ V := Nat.mul_le_mul HD (hH r t)
    _ = 2 ^ (V + (s.erase i).card * G) := by rw [← pow_add]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide)
      (Nat.add_le_add_left (Nat.mul_le_mul_right G (Finset.card_erase_le)) V)

end LeanCanny.Algebra.CommonIntegerDenominator

namespace LeanCanny.Algebra.UniformIntegralPrefix
open FixedWidthPolynomial
set_option backward.isDefEq.respectTransparency false
variable {S B m n : ℕ} {P : Prefix S (2 ^ B) m} {Q : Prefix S (2 ^ B) n}

theorem Chain.entry_height (C : Chain S B P Q) (x : P.carrier) (H : ℕ)
    (hx : ∀ r t, (Algebra.leftMulMatrix P.basis.finBasis x r t).natAbs ≤ 2 ^ H)
    (i j : Fin (count n B)) :
    (Algebra.leftMulMatrix Q.basis.finBasis (C.embed x) i j).natAbs ≤ 2 ^ H := by
  rw [C.matrix]
  split_ifs
  · exact hx _ _
  · exact Nat.zero_le _

end LeanCanny.Algebra.UniformIntegralPrefix

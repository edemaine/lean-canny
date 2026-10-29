/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineConeFlag
public import LeanCanny.Algebra.FermatCriticalHomogenization

/-! # Initial transverse flags for pure-power leading forms

The gradient of a nonzero scalar multiple of the sum of D-th powers vanishes
only at the origin in characteristic zero when D is at least two. Thus the
empty flag satisfies the all-extension invariant used by bounded affine
cone directions.
-/

@[expose] public section
namespace LeanCanny.Algebra.FermatAffineConeFlag
open MvPolynomial AffineConeFlag AffineConeBoundedDirection
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} {n : ℕ} [Field K]

noncomputable def form (a : K) (D : ℕ) : MvPolynomial (Fin n) K := C a * ∑ i, X i ^ D

theorem homogeneous (a : K) (D : ℕ) : (form (n := n) a D).IsHomogeneous D := by
  apply IsHomogeneous.C_mul
  apply IsHomogeneous.sum
  intro i _
  simpa only [one_mul] using (isHomogeneous_X (R := K) i).pow D

theorem pderiv_form (a : K) (D : ℕ) (i : Fin n) :
    pderiv i (form a D) = C (a * (D : K)) * X i ^ (D - 1) := by
  have hs : pderiv i (∑ j : Fin n, (X j : MvPolynomial (Fin n) K) ^ D) =
      C (D : K) * X i ^ (D - 1) := by
    rw [map_sum, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [pderiv_pow, pderiv_X_of_ne hji, mul_zero]
    · simp
  rw [form, pderiv_C_mul, hs, ← mul_assoc, ← map_mul]

variable [CharZero K]

theorem gradient_ne_zero {L : Type u} [Field L] [Algebra K L]
    (a : K) (ha : a ≠ 0) (D : ℕ) (hD : 1 < D) (x : Fin n → L) (hx : x ≠ 0) :
    ∃ i, aeval x (pderiv i (form a D)) ≠ 0 := by
  let _ : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! H
    apply hx
    funext i
    exact H i
  have ha' : algebraMap K L a ≠ 0 := by
    intro he
    apply ha
    apply (algebraMap K L).injective
    simpa only [map_zero] using he
  refine ⟨i, ?_⟩
  rw [pderiv_form, map_mul, aeval_C, map_pow, aeval_X, map_mul, map_natCast]
  exact mul_ne_zero (mul_ne_zero ha' (Nat.cast_ne_zero.mpr (by omega)))
    (pow_ne_zero _ hi)

/-- This initial flag needs no assumption about real or complex affine levels. -/
theorem transverse_empty (a : K) (ha : a ≠ 0) (D : ℕ) (hD : 1 < D)
    (A : Fin n → Fin n → K) (L : Type u) [Field L] [Algebra K L] :
    Transverse (L := L) (form a D) ∅ A := by
  exact AffineConeFlag.transverse_empty (form a D) A (fun x _ hx => gradient_ne_zero a ha D hD x hx)

/-- The first affine normal for the pure-power cone has the same explicit
bit bound as every later transverse flag extension. -/
theorem exists_first_bounded (a : K) (ha : a ≠ 0) (D : ℕ) (hD : 1 < D)
    (A : Fin n → Fin n → K) (r : Fin n) :
    ∃ v : Fin n → ℕ, (∀ i, v i < 2 ^ binaryWidth n D) ∧
      ∀ (L : Type u) [Field L] [Algebra K L],
        Transverse (L := L) (form a D) {r} (Function.update A r (fun i => (v i : K))) := by
  simpa only [Finset.insert_empty] using exists_bounded_extension (form a D) D (homogeneous a D) hD
    ∅ (by simpa only [Finset.card_empty] using r.pos) A r (by simp) (transverse_empty a ha D hD A)

omit [CharZero K] in
theorem original_leading_form (a : K) (D : ℕ) :
    FermatCriticalHomogenization.polynomial (0 : MvPolynomial (Fin (n + 1)) K) a D = form a D := by
  simp only [FermatCriticalHomogenization.polynomial, zero_add, form]

end LeanCanny.Algebra.FermatAffineConeFlag

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedVirtualSweepSource
public import LeanCanny.Algebra.IntegralNilpotentMatrix

/-! # Actual old-prefix leaves of virtual swept heights

The swept common-cleared height is an old algebra element plus one
integer multiple of the formal parameter. Its virtual multiplication
matrix has the old height matrix on equal digits, an integer identity
block one digit below, and zero everywhere else. No new retained scalar
reader is needed for the formal nilpotent.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualHeight
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralCoordinateBasis FixedWidthPolynomial Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def constant (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (i : ℕ) :=
  CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales
    (fun j => expression x (r.critical.heights j)) i

noncomputable def slope (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (i : ℕ) : ℤ :=
  if hi : i < n + 1 then
    if (⟨i, hi⟩ : Fin (n + 1)) = r.height then r.slope *
      CommonIntegerDenominator.denominator (Finset.univ.erase ⟨i, hi⟩) (data x hm r.critical).scales else 0
  else 0

theorem polynomial_eq (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (i : ℕ) :
    CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales (heights x r) i =
      C (constant x hm r i) + C (slope x hm r i : x.sampler.scalarPrefix.carrier) * X := by
  unfold constant slope
  unfold CoordinateFrozenCriticalElimination.numerators
  split_ifs with hi hindex
  · unfold CommonIntegerDenominator.numerator heights
    rw [ite_eq_left hindex]
    simp only [Int.cast_mul, map_mul, ← Polynomial.C_eq_intCast]
    ring
  · unfold CommonIntegerDenominator.numerator heights
    rw [ite_eq_right hindex]
    simp only [Int.cast_zero, map_zero, zero_mul, add_zero, ← Polynomial.C_eq_intCast, map_mul]
  · simp only [Int.cast_zero, map_zero, zero_mul, add_zero]

theorem coefficient_zero (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (i : ℕ) :
    (CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales (heights x r) i).coeff 0 =
      constant x hm r i := by rw [polynomial_eq]; simp

theorem coefficient_one (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (i : ℕ) :
    (CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales (heights x r) i).coeff 1 =
      (slope x hm r i : x.sampler.scalarPrefix.carrier) := by rw [polynomial_eq]; simp

theorem coefficient_other (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (i k : ℕ)
    (h0 : k ≠ 0) (h1 : k ≠ 1) :
    (CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales (heights x r) i).coeff k = 0 := by
  rw [polynomial_eq]
  have HC (a b : x.sampler.scalarPrefix.carrier) : (C a + C b * X).coeff k = 0 := by
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
      ite_eq_right h0, ite_eq_right h1, add_zero]
  exact HC _ _

theorem matrix (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (i : ℕ)
    (u v : Fin (count m B)) (e h : Fin (2 ^ B)) :
    Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis x).finBasis
      (AdjoinRoot.mk (X ^ (2 ^ B))
        (CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales (heights x r) i))
      (pairIndex m B (u, e)) (pairIndex m B (v, h)) =
      if e.val = h.val then Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (constant x hm r i) u v
      else if e.val = h.val + 1 then (slope x hm r i) * (if u = v then 1 else 0) else 0 := by
  unfold IntegralMixedCutNilpotent.basis
  rw [IntegralNilpotentMatrix.fixedWidth]
  by_cases H : h.val ≤ e.val
  · rw [ite_eq_left H]
    by_cases H0 : e.val = h.val
    · rw [ite_eq_left H0, Nat.sub_eq_zero_of_le (by omega), coefficient_zero]
    · rw [ite_eq_right H0]
      by_cases H1 : e.val = h.val + 1
      · rw [ite_eq_left H1, show e.val - h.val = 1 from by omega, coefficient_one,
          map_intCast, Matrix.intCast_apply]
        split_ifs <;> simp only [mul_one, mul_zero] <;> rfl
      · rw [ite_eq_right H1, coefficient_other x hm r i _ (by omega) (by omega), map_zero, Matrix.zero_apply]
  · rw [ite_eq_right H, ite_eq_right (by omega), ite_eq_right (by omega)]

end LeanCanny.Algebra.IntegralMixedVirtualHeight

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SubresultantBounds
public import LeanCanny.Algebra.PrincipalSubresultant.Minor

/-! # Parameter-degree bounds for signed principal coefficients

The formal outer degree bounds may exceed the specialized degrees. Uniform
parameter-degree bounds on the original coefficients still control every
principal test, including terminal and empty minors.
-/

@[expose] public section
namespace LeanCanny.Algebra.PrincipalSubresultant
open Polynomial

theorem signedPsc_parameter_degree {R : Type*} [CommRing R]
    (p q : (R[X])[X]) (m n j D : ℕ)
    (hp : ∀ i, (p.coeff i).natDegree ≤ D) (hq : ∀ i, (q.coeff i).natDegree ≤ D) :
    (signedPsc p q m n j).natDegree ≤ (m + n + 1) * D := by
  have hD : D ≤ (m + n + 1) * D := by
    simpa only [one_mul] using Nat.mul_le_mul_right D (show 1 ≤ m + n + 1 by omega)
  by_cases hj : j ≤ min m n
  · rw [signedPsc_of_le p q hj, psc_eq_minor]
    have hs : ((-1 : R[X]) ^ (m - j).choose 2).natDegree = 0 := by
      simp only [← Polynomial.C_neg, ← Polynomial.C_1, ← Polynomial.C_pow, Polynomial.natDegree_C]
    have hd := Subresultant.minor_natDegree_le p q m n j j D D hp hq
    apply Polynomial.natDegree_mul_le.trans
    rw [hs, zero_add]
    apply hd.trans
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right D (by omega)
  · rw [signedPsc_of_lt p q (by omega)]
    split_ifs
    · exact (hp _).trans hD
    · exact (hq _).trans hD
    · simp

end LeanCanny.Algebra.PrincipalSubresultant

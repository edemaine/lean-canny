/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableSlice
public import LeanCanny.Algebra.UnivariateRationalComposition

/-! # Parameter slices of symbolic denominator-cleared composition

The original root exponent remains the exponent of the numerator and
complementary denominator power. Parameter monomials are separate factors.
-/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicCoordinateClear
open Polynomial
open scoped Classical BigOperators
variable {R : Type*} [CommRing R]

lemma encode_clear (B e : ℕ) (p n d : Polynomial (Polynomial R)) :
    PolynomialKronecker.encode B (UnivariateRational.clear e p n d) =
      ∑ j ∈ Finset.range (e + 1), p.coeff j * (PolynomialKronecker.encode B n) ^ j *
        (PolynomialKronecker.encode B d) ^ (e - j) := by
  simp only [UnivariateRational.clear, map_sum, map_mul, map_pow, PolynomialKronecker.encode_C]

/-- Slicing the parameter first retains the root exponent used for clearing.
In particular, the encoded source polynomial is never used as a root source. -/
lemma encode_clear_slices (B e A : ℕ) (p n d : Polynomial (Polynomial R))
    (hA : ∀ j, (p.coeff j).natDegree ≤ A) :
    PolynomialKronecker.encode B (UnivariateRational.clear e p n d) =
      ∑ l ∈ Finset.range (A + 1), X ^ l *
        UnivariateRational.clear e (SymbolicFixedTable.slice p l)
          (PolynomialKronecker.encode B n) (PolynomialKronecker.encode B d) := by
  rw [encode_clear]
  simp only [UnivariateRational.clear, SymbolicFixedTable.slice_coeff, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hp : (p.coeff j).natDegree < A + 1 := Nat.lt_succ_of_le (hA j)
  calc
    _ = (∑ l ∈ Finset.range (A + 1), C ((p.coeff j).coeff l) * X ^ l) *
        (PolynomialKronecker.encode B n) ^ j * (PolynomialKronecker.encode B d) ^ (e - j) := by
      congr 2
      exact (p.coeff j).as_sum_range_C_mul_X_pow' hp
    _ = _ := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring

end LeanCanny.Algebra.SymbolicCoordinateClear

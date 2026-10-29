/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleFilters
public import LeanCanny.Encoding.SquareSampleTestMoments
public import LeanCanny.Algebra.PolynomialSumSquaresSpace

/-! # One native polynomial test for all square-system equations

A sum of squares of the cleared equation polynomials vanishes exactly at
the accepted real parameter roots. No Jacobian test is included.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleEquationTest
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open SquareSampleInput (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

noncomputable def polynomial (F : Inputs) := PolynomialSumSquaresBits.polynomial (SquareSampleFilters.polynomial F) F.count
noncomputable def degree (F : Inputs) (u : List Bool) : ℕ := 2 * SquareSampleFilters.degree F u
noncomputable def mass (F : Inputs) (u : List Bool) : ℕ := (F.count u).size + 2 * SquareSampleFilters.mass F u

lemma polynomial_degree (F : Inputs) (u : List Bool) : (polynomial F u).natDegree ≤ degree F u := by
  unfold polynomial PolynomialSumSquaresBits.polynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact Polynomial.natDegree_pow_le_of_le 2 (by
    simpa only [pairFst_pair] using SquareSampleFilters.polynomial_degree F (pair u (BinaryNatCode.encode i)))

lemma polynomial_mass (F : Inputs) (u : List Bool) : coefficientMass (polynomial F u) ≤ 2 ^ mass F u := by
  unfold polynomial PolynomialSumSquaresBits.polynomial
  apply (coefficientMass_sum_le _ _).trans
  have hrow (i : ℕ) : coefficientMass (SquareSampleFilters.polynomial F (pair u (BinaryNatCode.encode i)) ^ 2) ≤
      2 ^ (2 * SquareSampleFilters.mass F u) := by
    apply (coefficientMass_pow_le _ _).trans
    have h := SquareSampleFilters.polynomial_mass F (pair u (BinaryNatCode.encode i))
    simp only [pairFst_pair] at h
    exact (Nat.pow_le_pow_left h 2).trans_eq (by rw [← pow_mul, Nat.mul_comm])
  calc
    _ ≤ ∑ _i ∈ Finset.range (F.count u), 2 ^ (2 * SquareSampleFilters.mass F u) := Finset.sum_le_sum fun i _ => hrow i
    _ = F.count u * 2 ^ (2 * SquareSampleFilters.mass F u) := by simp
    _ ≤ 2 ^ (F.count u).size * 2 ^ (2 * SquareSampleFilters.mass F u) := Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
    _ = _ := (pow_add _ _ _).symm

noncomputable def test (F : Inputs) : SquareSampleTestMoments.Test where
  polynomial := polynomial F
  degree := degree F
  mass := mass F
  polynomial_degree := polynomial_degree F
  polynomial_mass := polynomial_mass F

noncomputable def access {F : Inputs} (h : F.Access) : (test F).Access :=
  SquareSampleTestMoments.Test.Access.ofPrimitive
    ((BinaryFn.const 2).mul (SquareSampleFilters.degree_binary h))
    ((BinaryFn.ofUnary h.count.size).add ((BinaryFn.const 2).mul (SquareSampleFilters.mass_binary h)))
    (PolynomialSumSquaresBits.evaluator _ _ (BinaryFn.ofUnary h.count) (SquareSampleFilters.evaluator h))

lemma zero_iff (F : Inputs) (u : List Bool) (theta : ℝ)
    (ht : (SquareSampleCoordinates.parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0) :
    (polynomial F u).eval₂ (Int.castRingHom ℝ) theta = 0 ↔
      ∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) (SquareSampleParameters.decode F u theta) = 0 := by
  change (∑ i ∈ Finset.range (F.count u), SquareSampleFilters.polynomial F (pair u (BinaryNatCode.encode i)) ^ 2).eval₂
    (Int.castRingHom ℝ) theta = 0 ↔ _
  rw [Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_pow]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  simp only [sq_eq_zero_iff, Finset.mem_range]
  constructor
  · intro h i
    exact (SquareSampleFilters.zero_packet F u i theta ht).mp (h i.val i.isLt)
  · intro h i hi
    exact (SquareSampleFilters.zero_packet F u ⟨i, hi⟩ theta ht).mpr (h ⟨i, hi⟩)

end LeanCanny.Encoding.SquareSampleEquationTest

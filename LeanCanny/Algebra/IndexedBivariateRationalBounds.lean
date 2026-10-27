/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IndexedRationalSubstitutionBounds
public import LeanCanny.Algebra.NestedCoefficientMass
public import LeanCanny.Algebra.PolynomialKronecker
public import LeanCanny.Algebra.ParameterizedTarski

/-! # Indexed denominator clearing in two independent variables

The clearing width is retained across specialization and modular reduction.
Repeated source monomials, cancellations, zero coordinates, and empty variable
families are allowed. All bounds use binary counts rather than expanded arrays.
-/

@[expose] public section
namespace LeanCanny.Algebra.RationalSubstitution.IndexedBivariate
open Polynomial
open scoped BigOperators Classical

noncomputable def cleared (A M W : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ)
    (n d : ℕ → (ℤ[X])[X]) : (ℤ[X])[X] :=
  Indexed.cleared A M W (fun r => Polynomial.C (a r)) e n d

theorem encode_cleared (B A M W : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ) (n d : ℕ → (ℤ[X])[X]) :
    PolynomialKronecker.encode B (cleared A M W a e n d) =
      Indexed.cleared A M W a e (fun i => PolynomialKronecker.encode B (n i))
        (fun i => PolynomialKronecker.encode B (d i)) := by
  simp only [cleared, Indexed.cleared, map_sum, map_mul, map_prod, map_pow, PolynomialKronecker.encode_C]

theorem outer_degree_le (A M W E : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ) (n d : ℕ → (ℤ[X])[X])
    (he : ∀ r, r < M → ∀ i, i < A → e r i ≤ W)
    (hn : ∀ i, i < A → (n i).natDegree ≤ E) (hd : ∀ i, i < A → (d i).natDegree ≤ E) :
    (cleared A M W a e n d).natDegree ≤ A * W * E :=
  Indexed.natDegree_cleared_le A M W E _ e n d he hn hd

theorem inner_degree_le (A M W E : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ) (n d : ℕ → (ℤ[X])[X])
    (he : ∀ r, r < M → ∀ i, i < A → e r i ≤ W)
    (hn : ∀ i, i < A → ∀ j, ((n i).coeff j).natDegree ≤ E)
    (hd : ∀ i, i < A → ∀ j, ((d i).coeff j).natDegree ≤ E) (j : ℕ) :
    ((cleared A M W a e n d).coeff j).natDegree ≤ A * W * E := by
  apply (PolynomialKronecker.inner_degree_iff_swap _ _).mpr ?_ j
  have hs : Polynomial.Bivariate.swap (cleared A M W a e n d) =
      cleared A M W a e (fun i => Polynomial.Bivariate.swap (n i)) (fun i => Polynomial.Bivariate.swap (d i)) := by
    simp only [cleared, Indexed.cleared, map_sum, map_mul, map_prod, map_pow, Polynomial.Bivariate.swap_C,
      Polynomial.map_C]
  rw [hs]
  exact outer_degree_le A M W E a e _ _ he
    (fun i hi => (PolynomialKronecker.inner_degree_iff_swap _ _).mp (hn i hi))
    (fun i hi => (PolynomialKronecker.inner_degree_iff_swap _ _).mp (hd i hi))

theorem mass_le (A M W s b : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ) (n d : ℕ → (ℤ[X])[X])
    (he : ∀ r, r < M → ∀ i, i < A → e r i ≤ W)
    (ha : ∀ r, r < M → (a r).natAbs ≤ 2 ^ s)
    (hn : ∀ i, i < A → NestedMass.mass (n i) ≤ 2 ^ b)
    (hd : ∀ i, i < A → NestedMass.mass (d i) ≤ 2 ^ b) :
    NestedMass.mass (cleared A M W a e n d) ≤ 2 ^ (M.size + s + A * W * b) := by
  have hf (r i : ℕ) (hr : r < M) (hi : i < A) :
      NestedMass.mass (n i ^ e r i * d i ^ (W - e r i)) ≤ 2 ^ (W * b) := by
    calc
      _ ≤ NestedMass.mass (n i ^ e r i) * NestedMass.mass (d i ^ (W - e r i)) := NestedMass.mul_le _ _
      _ ≤ NestedMass.mass (n i) ^ e r i * NestedMass.mass (d i) ^ (W - e r i) :=
        Nat.mul_le_mul (NestedMass.pow_le _ _) (NestedMass.pow_le _ _)
      _ ≤ (2 ^ b) ^ e r i * (2 ^ b) ^ (W - e r i) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (hn i hi) _) (Nat.pow_le_pow_left (hd i hi) _)
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le (he r hr i hi), ← pow_mul, Nat.mul_comm]
  have hp (r : ℕ) (hr : r < M) :
      NestedMass.mass (∏ i ∈ Finset.range A, n i ^ e r i * d i ^ (W - e r i)) ≤ 2 ^ (A * W * b) := by
    calc
      _ ≤ ∏ i ∈ Finset.range A, NestedMass.mass (n i ^ e r i * d i ^ (W - e r i)) := NestedMass.prod_le _ _
      _ ≤ ∏ _i ∈ Finset.range A, 2 ^ (W * b) :=
        Finset.prod_le_prod (fun i hi => hf r i hr (Finset.mem_range.mp hi))
      _ = _ := by simp only [Finset.prod_const, Finset.card_range, ← pow_mul]; congr 1; ring
  have ht (r : ℕ) (hr : r < M) :
      NestedMass.mass (C (C (a r)) * ∏ i ∈ Finset.range A, n i ^ e r i * d i ^ (W - e r i)) ≤
        2 ^ (s + A * W * b) := by
    apply (NestedMass.mul_le _ _).trans
    rw [NestedMass.C, coefficientMass_C, pow_add]
    exact Nat.mul_le_mul (ha r hr) (hp r hr)
  calc
    _ ≤ ∑ r ∈ Finset.range M,
        NestedMass.mass (C (C (a r)) * ∏ i ∈ Finset.range A, n i ^ e r i * d i ^ (W - e r i)) := NestedMass.sum_le _ _
    _ ≤ ∑ _r ∈ Finset.range M, 2 ^ (s + A * W * b) :=
      Finset.sum_le_sum (fun r hr => ht r (Finset.mem_range.mp hr))
    _ = M * 2 ^ (s + A * W * b) := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ 2 ^ M.size * 2 ^ (s + A * W * b) := Nat.mul_le_mul_right _ (Nat.lt_size_self M).le
    _ = _ := by rw [← pow_add, Nat.add_assoc]

theorem specialize (β : ℝ) (A M W : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ) (n d : ℕ → (ℤ[X])[X]) :
    (cleared A M W a e n d).map (ParameterTarski.evalHom β) =
      Indexed.cleared A M W (fun r => (a r : ℝ)) e
        (fun i => (n i).map (ParameterTarski.evalHom β)) (fun i => (d i).map (ParameterTarski.evalHom β)) := by
  rw [cleared, Indexed.map_cleared]
  simp only [ParameterTarski.evalHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Int.coe_castRingHom]

end LeanCanny.Algebra.RationalSubstitution.IndexedBivariate

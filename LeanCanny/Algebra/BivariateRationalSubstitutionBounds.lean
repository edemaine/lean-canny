/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitutionWith
public import LeanCanny.Algebra.NestedCoefficientMass
public import LeanCanny.Algebra.PolynomialKronecker
public import LeanCanny.Algebra.MvCoefficientMass

/-! # Bounds for uniform denominator clearing over an integer parameter ring -/

@[expose] public section
namespace LeanCanny.Algebra.BivariateRationalSubstitution
open Polynomial
open scoped BigOperators Classical

variable {σ : Type*} [Fintype σ]

noncomputable def sourceMass (p : MvPolynomial σ ℤ[X]) : ℕ :=
  ∑ e ∈ p.support, coefficientMass (p.coeff e)

theorem mass_clearedWith (p : MvPolynomial σ ℤ[X]) (D : σ → ℕ)
    (n d : σ → (ℤ[X])[X]) (M : σ → ℕ)
    (hD : ∀ i, p.degreeOf i ≤ D i)
    (hn : ∀ i, NestedMass.mass (n i) ≤ M i) (hd : ∀ i, NestedMass.mass (d i) ≤ M i) :
    NestedMass.mass (RationalSubstitution.clearedWith D p n d) ≤
      sourceMass p * ∏ i, M i ^ (2 * D i) := by
  have hf (e : σ →₀ ℕ) (he : e ∈ p.support) (i : σ) :
      NestedMass.mass (n i ^ e i * d i ^ (2 * D i - e i)) ≤ M i ^ (2 * D i) := by
    have hm : e i ≤ 2 * D i := (MvPolynomial.monomial_le_degreeOf i he).trans (by have := hD i; omega)
    calc
      _ ≤ NestedMass.mass (n i ^ e i) * NestedMass.mass (d i ^ (2 * D i - e i)) := NestedMass.mul_le _ _
      _ ≤ NestedMass.mass (n i) ^ e i * NestedMass.mass (d i) ^ (2 * D i - e i) :=
        Nat.mul_le_mul (NestedMass.pow_le _ _) (NestedMass.pow_le _ _)
      _ ≤ M i ^ e i * M i ^ (2 * D i - e i) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (hn i) _) (Nat.pow_le_pow_left (hd i) _)
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hm]
  unfold RationalSubstitution.clearedWith
  calc
    _ ≤ ∑ e ∈ p.support,
        NestedMass.mass (C (p.coeff e) * ∏ i, n i ^ e i * d i ^ (2 * D i - e i)) := NestedMass.sum_le _ _
    _ ≤ ∑ e ∈ p.support, coefficientMass (p.coeff e) * ∏ i, M i ^ (2 * D i) := by
      apply Finset.sum_le_sum
      intro e he
      apply (NestedMass.mul_le _ _).trans
      rw [NestedMass.C]
      exact Nat.mul_le_mul_left _ ((NestedMass.prod_le _ _).trans (Finset.prod_le_prod (fun i _ => hf e he i)))
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem mass_clearedWith_uniform (p : MvPolynomial σ ℤ[X]) (D s b : ℕ)
    (n d : σ → (ℤ[X])[X]) (hD : ∀ i, p.degreeOf i ≤ D)
    (hp : sourceMass p ≤ 2 ^ s)
    (hn : ∀ i, NestedMass.mass (n i) ≤ 2 ^ b) (hd : ∀ i, NestedMass.mass (d i) ≤ 2 ^ b) :
    NestedMass.mass (RationalSubstitution.clearedWith (fun _ => D) p n d) ≤
      2 ^ (s + 2 * Fintype.card σ * D * b) := by
  have he : (∏ _i : σ, (2 ^ b) ^ (2 * D)) = 2 ^ (2 * Fintype.card σ * D * b) := by
    simp only [Finset.prod_const, Finset.card_univ, ← pow_mul]
    congr 1
    ring
  exact (mass_clearedWith p _ n d _ hD hn hd).trans
    ((Nat.mul_le_mul_right _ hp).trans_eq (by rw [he, ← pow_add]))

theorem outer_degree_clearedWith {R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (D E : ℕ) (n d : σ → R[X])
    (hD : ∀ i, p.degreeOf i ≤ D)
    (hn : ∀ i, (n i).natDegree ≤ E) (hd : ∀ i, (d i).natDegree ≤ E) :
    (RationalSubstitution.clearedWith (fun _ => D) p n d).natDegree ≤ 2 * Fintype.card σ * D * E := by
  apply (RationalSubstitution.natDegree_clearedWith_le (fun _ => D) p n d hD E hn hd).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

theorem inner_degree_clearedWith (p : MvPolynomial σ ℤ[X]) (D Ep E : ℕ)
    (n d : σ → (ℤ[X])[X]) (hD : ∀ i, p.degreeOf i ≤ D)
    (hp : ∀ e, (p.coeff e).natDegree ≤ Ep)
    (hn : ∀ i k, ((n i).coeff k).natDegree ≤ E) (hd : ∀ i k, ((d i).coeff k).natDegree ≤ E) (j : ℕ) :
    ((RationalSubstitution.clearedWith (fun _ => D) p n d).coeff j).natDegree ≤
      Ep + 2 * Fintype.card σ * D * E := by
  apply (PolynomialKronecker.inner_degree_iff_swap _ _).mpr ?_ j
  unfold RationalSubstitution.clearedWith
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  rw [map_mul, map_prod, Polynomial.Bivariate.swap_C]
  have hf (i : σ) :
      (Polynomial.Bivariate.swap (n i ^ e i * d i ^ (2 * D - e i))).natDegree ≤ 2 * D * E := by
    have hm : e i ≤ 2 * D := (MvPolynomial.monomial_le_degreeOf i he).trans (by have := hD i; omega)
    rw [map_mul, map_pow, map_pow]
    calc
      _ ≤ (Polynomial.Bivariate.swap (n i) ^ e i).natDegree +
          (Polynomial.Bivariate.swap (d i) ^ (2 * D - e i)).natDegree := natDegree_mul_le
      _ ≤ e i * E + (2 * D - e i) * E := Nat.add_le_add
        (natDegree_pow_le.trans (Nat.mul_le_mul_left _ ((PolynomialKronecker.inner_degree_iff_swap _ _).mp (hn i))))
        (natDegree_pow_le.trans (Nat.mul_le_mul_left _ ((PolynomialKronecker.inner_degree_iff_swap _ _).mp (hd i))))
      _ = _ := by rw [← Nat.add_mul, Nat.add_sub_of_le hm]
  apply natDegree_mul_le.trans
  apply Nat.add_le_add (natDegree_map_le.trans (hp e))
  calc
    _ ≤ ∑ i, (Polynomial.Bivariate.swap (n i ^ e i * d i ^ (2 * D - e i))).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _i : σ, 2 * D * E := Finset.sum_le_sum (fun i _ => hf i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring

omit [Fintype σ] in
theorem sourceMass_map_int (p : MvPolynomial σ ℤ) :
    sourceMass (p.map (Int.castRingHom ℤ[X])) = MvMass.mass p := by
  unfold sourceMass MvMass.mass
  rw [MvPolynomial.support_map_of_injective _ (show Function.Injective (Int.castRingHom ℤ[X]) from Polynomial.C_injective)]
  apply Finset.sum_congr rfl
  intro e _
  rw [MvPolynomial.coeff_map]
  change coefficientMass (Polynomial.C (p.coeff e)) = _
  exact coefficientMass_C _

end LeanCanny.Algebra.BivariateRationalSubstitution

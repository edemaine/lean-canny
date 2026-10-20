/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayMultiplicationMatrix

/-! # Koszul relations in the finite graded multiplication matrix

The multiplier family with components m*fⱼ and -m*fᵢ gives a zero polynomial
combination. When its degrees fit the Macaulay level, coefficient reconstruction
turns it into a finite left-kernel vector of the full rectangular matrix.
This does not assert that these vectors span the kernel or yield determinant
cancellation for the selected square matrix.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def koszulMultipliers (p : Fin n → MvPolynomial (Fin n) R) (i j : Fin n) (m : Fin n →₀ ℕ) :
    Fin n → MvPolynomial (Fin n) R :=
  Pi.single i (MvPolynomial.monomial m 1 * p j) - Pi.single j (MvPolynomial.monomial m 1 * p i)

theorem koszul_polynomial_relation (p : Fin n → MvPolynomial (Fin n) R) (i j : Fin n) (m : Fin n →₀ ℕ) :
    (∑ k, koszulMultipliers p i j m k * p k) = 0 := by
  simp only [koszulMultipliers, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

private theorem degree_of_support (q : MvPolynomial (Fin n) R) (t : ℕ) (hq : q.IsHomogeneous t)
    (m : Fin n →₀ ℕ) (hm : m ∈ q.support) : m.degree = t := by
  by_contra h
  exact (MvPolynomial.mem_support_iff.mp hm) (hq.coeff_eq_zero h)

theorem koszul_multiplier_grade (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hp : ∀ k, (p k).IsHomogeneous (d k)) (i j : Fin n) (hij : i ≠ j) (m : Fin n →₀ ℕ)
    (hm : m.degree + d i + d j = level d) :
    ∀ k e, e ∈ (koszulMultipliers p i j m k).support → e.degree + d k = level d := by
  intro k e he
  by_cases hki : k = i
  · subst k
    have hh := (MvPolynomial.isHomogeneous_monomial (d := m) (1 : R) rfl).mul (hp j)
    have hs : e ∈ (MvPolynomial.monomial m 1 * p j).support := by
      simpa [koszulMultipliers, Pi.single_apply, hij, hij.symm] using he
    have hg := degree_of_support _ _ hh e hs
    omega
  · by_cases hkj : k = j
    · subst k
      have hh := ((MvPolynomial.isHomogeneous_monomial (d := m) (1 : R) rfl).mul (hp i)).neg
      have hs : e ∈ (-(MvPolynomial.monomial m 1 * p i)).support := by
        simpa [koszulMultipliers, Pi.single_apply, hij, hij.symm] using he
      have hg := degree_of_support _ _ hh e hs
      omega
    · simp [koszulMultipliers, hki, hkj] at he

theorem koszul_vecMul_eq_zero (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ k, (p k).IsHomogeneous (d k)) (hW : level d < 2 ^ W)
    (i j : Fin n) (hij : i ≠ j) (m : Fin n →₀ ℕ) (hm : m.degree + d i + d j = level d) :
    Matrix.vecMul (sourceCoefficients (koszulMultipliers p i j m) d W) (fullMatrix p d W) = 0 := by
  funext r
  change Matrix.vecMul (sourceCoefficients (koszulMultipliers p i j m) d W) (fullMatrix p d W) r = 0
  rw [vecMul_fullMatrix, assemble_coefficients p (koszulMultipliers p i j m) d W hW
    (koszul_multiplier_grade p d hp i j hij m hm), koszul_polynomial_relation]
  simp

theorem koszul_coefficients_ne_zero [IsDomain R] (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ k, (p k).IsHomogeneous (d k)) (hW : level d < 2 ^ W)
    (i j : Fin n) (hij : i ≠ j) (m : Fin n →₀ ℕ) (hm : m.degree + d i + d j = level d) (hpj : p j ≠ 0) :
    sourceCoefficients (koszulMultipliers p i j m) d W ≠ 0 := by
  intro hv
  have hr := multiplier_reconstruction (koszulMultipliers p i j m i) d W i hW
    (koszul_multiplier_grade p d hp i j hij m hm i)
  have hz : (∑ r : multiplierIndices d W i,
      MvPolynomial.monomial (FixedWidthPolynomial.vector n W r.val)
        ((koszulMultipliers p i j m i).coeff (FixedWidthPolynomial.vector n W r.val))) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    have hc := congrFun hv (⟨i, r⟩ : MultiplierIndex d W)
    change (koszulMultipliers p i j m i).coeff (FixedWidthPolynomial.vector n W r.val) = 0 at hc
    rw [hc, map_zero]
  have hqi : koszulMultipliers p i j m i = 0 := hr.symm.trans hz
  have hmono : (MvPolynomial.monomial m (1 : R)) ≠ 0 := by simp
  apply (mul_ne_zero hmono hpj)
  simpa [koszulMultipliers, Pi.single_apply, hij, hij.symm] using hqi

end LeanCanny.Algebra.Macaulay

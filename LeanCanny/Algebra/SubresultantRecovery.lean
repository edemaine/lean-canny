/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitiveResultant
public import LeanCanny.Algebra.SubresultantGCD

/-!
# Symbolic subresultant coordinate recovery

The first subresultant of `p₁(θ-c*x)` and `p₂(x)` supplies parameter polynomials
`N(θ)` and `D(θ)`. At a separating root pair, with nonzero direction and both
input degrees greater than one, `D(θ)≠0`, `b=-N(θ)/D(θ)`, and
`a=θ+c*N(θ)/D(θ)`. `CoordinateRecovery` handles linear inputs directly.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

noncomputable def recoverySubresultant {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c : ℕ) : Polynomial (Polynomial R) :=
  Subresultant.polynomial (shiftFamily p₁ c) (p₂.map C) p₁.natDegree p₂.natDegree 1

noncomputable def subresultantNumerator {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c : ℕ) : Polynomial R := (recoverySubresultant p₁ p₂ c).coeff 0

noncomputable def subresultantDenominator {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c : ℕ) : Polynomial R := (recoverySubresultant p₁ p₂ c).coeff 1

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem recoverySubresultant_specialize (p₁ p₂ : Polynomial K) (c : ℕ) (θ : L) :
    (recoverySubresultant p₁ p₂ c).map ((Polynomial.aeval θ : Polynomial K →ₐ[K] L) : Polynomial K →+* L) =
      Subresultant.polynomial (shiftedPolynomial p₁ c θ) (p₂.map (algebraMap K L)) p₁.natDegree p₂.natDegree 1 := by
  rw [recoverySubresultant, ← Subresultant.polynomial_map, shiftFamily_specialize,
    Polynomial.map_map, specialize_comp_C]

theorem shiftedPolynomial_natDegree (p : Polynomial K) (c : ℕ) (θ : L) (hc : (c : L) ≠ 0) :
    (shiftedPolynomial p c θ).natDegree = p.natDegree := by
  have hlinear : (C θ - C (c : L) * X : Polynomial L).natDegree = 1 := by
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt (by
      rw [Polynomial.natDegree_C_mul hc]
      simp), Polynomial.natDegree_C_mul hc, Polynomial.natDegree_X]
  rw [shiftedPolynomial, Polynomial.natDegree_comp, Polynomial.natDegree_map, hlinear, mul_one]

theorem subresultant_recovery_spec (p₁ p₂ : Polynomial K) (c : ℕ) (a b : L)
    (h₁ : p₁ ≠ 0) (h₂ : p₂.Separable) (hs₂ : (p₂.map (algebraMap K L)).Splits)
    (hm : 1 < p₁.natDegree) (hn : 1 < p₂.natDegree) (hc : (c : L) ≠ 0)
    (hinj : Set.InjOn (shear c) (rootPairs (L := L) p₁ p₂ : Set (L × L)))
    (ha : Polynomial.aeval a p₁ = 0) (hb : Polynomial.aeval b p₂ = 0) :
    let θ := shear c (a, b)
    let N := Polynomial.aeval θ (subresultantNumerator p₁ p₂ c)
    let D := Polynomial.aeval θ (subresultantDenominator p₁ p₂ c)
    D ≠ 0 ∧ b = -N / D ∧ a = θ + (c : L) * (N / D) := by
  classical
  let θ := shear c (a, b)
  let f := shiftedPolynomial p₁ c θ
  let g := p₂.map (algebraMap K L)
  have hdegf : f.natDegree = p₁.natDegree := shiftedPolynomial_natDegree p₁ c θ hc
  have hdegg : g.natDegree = p₂.natDegree := Polynomial.natDegree_map _
  have hgcd : EuclideanDomain.gcd f g = C (recoveryGCD p₁ p₂ c θ).leadingCoeff * (X - C b) :=
    recoveryGCD_eq_linear p₁ p₂ c a b h₁ h₂ hs₂ hinj ha hb
  have hl : (recoveryGCD p₁ p₂ c θ).leadingCoeff ≠ 0 :=
    mt Polynomial.leadingCoeff_eq_zero.mp (recoveryGCD_separable p₁ p₂ c θ h₂).ne_zero
  obtain ⟨_, hden, hratio⟩ := Subresultant.first_spec_of_linear_gcd f g b _ hl
    (by rw [hdegf]; exact hm) (by rw [hdegg]; exact hn) hgcd
  rw [hdegf, hdegg] at hden hratio
  have hN : Polynomial.aeval θ (subresultantNumerator p₁ p₂ c) =
      (Subresultant.polynomial f g p₁.natDegree p₂.natDegree 1).coeff 0 := by
    rw [← recoverySubresultant_specialize p₁ p₂ c θ, Polynomial.coeff_map]
    rfl
  have hD : Polynomial.aeval θ (subresultantDenominator p₁ p₂ c) =
      (Subresultant.polynomial f g p₁.natDegree p₂.natDegree 1).coeff 1 := by
    rw [← recoverySubresultant_specialize p₁ p₂ c θ, Polynomial.coeff_map]
    rfl
  dsimp only
  rw [hN, hD]
  refine ⟨hden, hratio, ?_⟩
  have hratio' : (Subresultant.polynomial f g p₁.natDegree p₂.natDegree 1).coeff 0 /
      (Subresultant.polynomial f g p₁.natDegree p₂.natDegree 1).coeff 1 = -b := by
    rw [neg_div] at hratio
    exact neg_eq_iff_eq_neg.mp hratio.symm
  rw [hratio']
  dsimp [θ, shear]
  ring

end LeanCanny.Algebra

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteAnnihilatorPolynomials
public import LeanCanny.Algebra.RationalSubstitutionWith

/-! # Polynomial constraints on explicit annihilator coordinates

Fixed even clearing allowances turn multivariate constraints into integer
univariate queries. At parameter roots, these queries preserve zeros and real
signs. An annihilator hypothesis gives a scalar-root characterization of the
original polynomial system without assuming an interpolated representation.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteAnnihilatorTree
open Polynomial
open scoped BigOperators

variable (p : ℕ → ℤ[X]) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)

noncomputable def constraint (D : Fin n → ℕ) (f : MvPolynomial (Fin n) ℤ) : ℤ[X] :=
  RationalSubstitution.clearedWith D f (numerator p n hp) (denominator p n hp)

theorem constraint_degree (D : Fin n → ℕ) (f : MvPolynomial (Fin n) ℤ)
    (hD : ∀ i, f.degreeOf i ≤ D i) (B : ℕ) (h1 : 1 ≤ B) (hB : ∀ i < n, (p i).natDegree ≤ B) :
    (constraint p n hp D f).natDegree ≤ (∑ i, 2 * D i) * (B + 2) ^ (4 * (n + 1)) := by
  apply RationalSubstitution.natDegree_clearedWith_le D f _ _ hD _
  · intro i
    exact (le_max_left _ _).trans (coordinate_degree p n hp B h1 hB i)
  · intro i
    exact (le_max_right _ _).trans (coordinate_degree p n hp B h1 hB i)

variable {K : Type*} [Field K] [CharZero K]

theorem constraint_eval (D : Fin n → ℕ) (f : MvPolynomial (Fin n) ℤ)
    (hD : ∀ i, f.degreeOf i ≤ D i) (theta : K)
    (ht : (parameter p n hp).polynomial.eval₂ (Int.castRingHom K) theta = 0) :
    (constraint p n hp D f).eval₂ (Int.castRingHom K) theta =
      (∏ i, (denominator p n hp i).eval₂ (Int.castRingHom K) theta ^ (2 * D i)) *
        f.eval₂ (Int.castRingHom K) (decode p n hp theta) := by
  rw [constraint, RationalSubstitution.eval₂_clearedWith _ _ D f _ _ hD
    (fun i => (coordinate_spec p n hp theta ht i).1)]
  congr 1
  exact congrArg (fun x : Fin n → K => f.eval₂ (Int.castRingHom K) x)
    (funext fun i => (coordinate_spec p n hp theta ht i).2)

theorem constraint_zero_iff (D : Fin n → ℕ) (f : MvPolynomial (Fin n) ℤ)
    (hD : ∀ i, f.degreeOf i ≤ D i) (theta : K)
    (ht : (parameter p n hp).polynomial.eval₂ (Int.castRingHom K) theta = 0) :
    (constraint p n hp D f).eval₂ (Int.castRingHom K) theta = 0 ↔
      f.eval₂ (Int.castRingHom K) (decode p n hp theta) = 0 := by
  have hfactor : (∏ i, (denominator p n hp i).eval₂ (Int.castRingHom K) theta ^ (2 * D i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (coordinate_spec p n hp theta ht i).1)
  rw [constraint_eval p n hp D f hD theta ht]
  simp only [mul_eq_zero, hfactor, false_or]

theorem constraint_sign (D : Fin n → ℕ) (f : MvPolynomial (Fin n) ℤ)
    (hD : ∀ i, f.degreeOf i ≤ D i) (theta : ℝ)
    (ht : (parameter p n hp).polynomial.eval₂ (Int.castRingHom ℝ) theta = 0) :
    SignType.sign ((constraint p n hp D f).eval₂ (Int.castRingHom ℝ) theta) =
      SignType.sign (f.eval₂ (Int.castRingHom ℝ) (decode p n hp theta)) := by
  have hfactor : 0 < ∏ i, (denominator p n hp i).eval₂ (Int.castRingHom ℝ) theta ^ (2 * D i) := by
    apply Finset.prod_pos
    intro i _
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero (coordinate_spec p n hp theta ht i).1) _
  rw [constraint_eval p n hp D f hD theta ht, sign_mul, sign_pos hfactor, one_mul]

theorem exists_solution_iff {τ : Type*} (D : τ → Fin n → ℕ) (f : τ → MvPolynomial (Fin n) ℤ)
    (hD : ∀ t i, (f t).degreeOf i ≤ D t i) :
    (∃ x : Fin n → K, (∀ i, (p i.val).eval₂ (Int.castRingHom K) (x i) = 0) ∧
      ∀ t, (f t).eval₂ (Int.castRingHom K) x = 0) ↔
    ∃ theta : K, (parameter p n hp).polynomial.eval₂ (Int.castRingHom K) theta = 0 ∧
      ∀ t, (constraint p n hp (D t) (f t)).eval₂ (Int.castRingHom K) theta = 0 := by
  constructor
  · rintro ⟨x, hx, hf⟩
    have ht := encode_root p n hp x hx
    refine ⟨encode p n hp x, ht, fun t => ?_⟩
    apply (constraint_zero_iff p n hp (D t) (f t) (hD t) _ ht).mpr
    rw [decode_encode p n hp x hx]
    exact hf t
  · rintro ⟨theta, ht, hf⟩
    exact ⟨decode p n hp theta, decode_root p n hp theta ht,
      fun t => (constraint_zero_iff p n hp (D t) (f t) (hD t) theta ht).mp (hf t)⟩

theorem exists_system_iff {τ : Type*} (D : τ → Fin n → ℕ) (f : τ → MvPolynomial (Fin n) ℤ)
    (hD : ∀ t i, (f t).degreeOf i ≤ D t i)
    (ha : ∀ x : Fin n → K, (∀ t, (f t).eval₂ (Int.castRingHom K) x = 0) →
      ∀ i, (p i.val).eval₂ (Int.castRingHom K) (x i) = 0) :
    (∃ x : Fin n → K, ∀ t, (f t).eval₂ (Int.castRingHom K) x = 0) ↔
    ∃ theta : K, (parameter p n hp).polynomial.eval₂ (Int.castRingHom K) theta = 0 ∧
      ∀ t, (constraint p n hp (D t) (f t)).eval₂ (Int.castRingHom K) theta = 0 := by
  rw [← exists_solution_iff p n hp D f hD]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, ha x hx, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩

end LeanCanny.Algebra.FiniteAnnihilatorTree

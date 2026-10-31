/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ScaledGradedReductionMatrix
public import LeanCanny.Algebra.GradedReductionAnnihilator
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Integral relative annihilators after denominator clearing

Clearing the reduction matrix's constant denominator scales its evaluation
row by c. The characteristic polynomial annihilates c^(bound+1) times the
selected value. Substituting that constant multiple of X recovers an integer
annihilator of the unscaled value, with the same specialized degree.
-/

@[expose] public section
namespace LeanCanny.Algebra.ScaledGradedReductionAnnihilator
open Matrix
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable {ι R K : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [Field K]

theorem padded_charpoly_root (T : Matrix ι ι R) (normal : ι → Prop) (degree : ι → ℕ) (c : R)
    (ha : ∀ j, normal j → ∀ i, T i j = if i = j then c else 0)
    (hd : ∀ i j, ¬normal j → T i j ≠ 0 → degree i < degree j)
    (bound : ℕ) (hbound : ∀ j, degree j ≤ bound) (shift : ι → ι)
    (φ : R →+* K) (v : ι → K) (hv : v ᵥ* T.map φ = φ c • v) (a : K)
    (hshift : ∀ j, normal j → v (shift j) = a * v j) (hne : ∃ i, normal i ∧ v i ≠ 0) :
    (GradedReductionAnnihilator.paddedMatrix T normal bound shift).charpoly.eval₂ φ
      ((φ c) ^ (bound + 1) * a) = 0 := by
  have ha' : ∀ j, normal j → ∀ i, (T.map φ) i j = if i = j then φ c else 0 := by
    intro j hj i
    rw [Matrix.map_apply, ha j hj i]
    split_ifs <;> simp only [map_zero]
  have hd' : ∀ i j, ¬normal j → (T.map φ) i j ≠ 0 → degree i < degree j := by
    intro i j hj hij
    apply hd i j hj
    intro H
    exact hij (by simp only [Matrix.map_apply, H, map_zero])
  apply FiniteSpanningAnnihilator.charpoly_root_of_relations
    (GradedReductionAnnihilator.paddedMatrix T normal bound shift) φ
      ((φ c) ^ (bound + 1) * a) (fun i => if normal i then v i else 0) ?_ ?_
  · obtain ⟨i, hi, hvi⟩ := hne
    exact ⟨i, by simpa only [ite_eq_left hi] using hvi⟩
  · intro j
    by_cases hj : normal j
    · have H := ScaledGradedReductionMatrix.normal_span (T.map φ) normal degree (φ c) ha' hd'
        bound hbound v hv (shift j)
      rw [← Matrix.map_pow] at H
      simp only [Matrix.map_apply] at H
      simp only [GradedReductionAnnihilator.paddedMatrix, ite_eq_left hj]
      calc
        _ = ∑ i ∈ Finset.univ.filter normal, v i * φ ((T ^ (bound + 1)) i (shift j)) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> simp only [zero_mul]
        _ = (φ c) ^ (bound + 1) * v (shift j) := H.symm
        _ = ((φ c) ^ (bound + 1) * a) * v j := by rw [hshift j hj, mul_assoc]
    · simp only [GradedReductionAnnihilator.paddedMatrix, ite_eq_right hj, map_zero,
        mul_zero, Finset.sum_const_zero]

noncomputable def polynomial (M : Matrix ι ι R) (c : R) (exponent : ℕ) : Polynomial R :=
  M.charpoly.comp (Polynomial.C (c ^ exponent) * Polynomial.X)

theorem coefficient (M : Matrix ι ι R) (c : R) (exponent k : ℕ) :
    (polynomial M c exponent).coeff k = M.charpoly.coeff k * c ^ (exponent * k) := by
  rw [polynomial, Polynomial.comp_C_mul_X_coeff, ← pow_mul]

theorem root (M : Matrix ι ι R) (c : R) (exponent : ℕ) (φ : R →+* K) (a : K)
    (h : M.charpoly.eval₂ φ ((φ c) ^ exponent * a) = 0) :
    (polynomial M c exponent).eval₂ φ a = 0 := by
  simpa only [polynomial, Polynomial.eval₂_comp, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, map_pow, Polynomial.eval₂_pow] using h

theorem map (M : Matrix ι ι R) (c : R) (exponent : ℕ) (φ : R →+* K) :
    (polynomial M c exponent).map φ = polynomial (M.map φ) (φ c) exponent := by
  simp only [polynomial, Polynomial.map_comp, Matrix.charpoly_map, Polynomial.map_mul,
    Polynomial.map_C, map_pow, Polynomial.map_pow, Polynomial.map_X]

theorem specialized_degree (M : Matrix ι ι R) (c : R) (exponent : ℕ) (φ : R →+* K)
    (hc : φ c ≠ 0) : ((polynomial M c exponent).map φ).natDegree = Fintype.card ι := by
  rw [map, polynomial, Polynomial.natDegree_comp, Matrix.charpoly_natDegree_eq_dim,
    Polynomial.natDegree_C_mul_X _ (pow_ne_zero _ hc), Nat.mul_one]

end LeanCanny.Algebra.ScaledGradedReductionAnnihilator

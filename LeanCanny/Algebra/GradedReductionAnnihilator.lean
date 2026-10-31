/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.GradedReductionMatrix
public import LeanCanny.Algebra.FiniteSpanningAnnihilator

/-! # Relative characteristic annihilators from bounded reductions

Select the normal rows of the reduction power and the columns representing
a chosen value times each normal monomial. Their characteristic polynomial
annihilates the value at every specialized root. Its degree is the normal
state count, independently of the rank of the old parameter algebra.
-/

@[expose] public section
namespace LeanCanny.Algebra.GradedReductionAnnihilator
open Matrix
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable {ι R K : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [Field K]

noncomputable def matrix (T : Matrix ι ι R) (normal : ι → Prop) (bound : ℕ)
    (shift : {i // normal i} → ι) : Matrix {i // normal i} {i // normal i} R :=
  fun i j => (T ^ (bound + 1)) i.val (shift j)

theorem charpoly_root (T : Matrix ι ι R) (normal : ι → Prop) (degree : ι → ℕ)
    (ha : ∀ j, normal j → ∀ i, T i j = if i = j then 1 else 0)
    (hd : ∀ i j, ¬normal j → T i j ≠ 0 → degree i < degree j)
    (bound : ℕ) (hbound : ∀ j, degree j ≤ bound) (shift : {i // normal i} → ι)
    (φ : R →+* K) (v : ι → K) (hv : v ᵥ* T.map φ = v) (a : K)
    (hshift : ∀ j, v (shift j) = a * v j.val) (hne : ∃ i : {i // normal i}, v i.val ≠ 0) :
    (matrix T normal bound shift).charpoly.eval₂ φ a = 0 := by
  have ha' : ∀ j, normal j → ∀ i, (T.map φ) i j = if i = j then 1 else 0 := by
    intro j hj i
    simp only [Matrix.map_apply, ha j hj i, apply_ite, map_one, map_zero]
    split_ifs <;> rfl
  have hd' : ∀ i j, ¬normal j → (T.map φ) i j ≠ 0 → degree i < degree j := by
    intro i j hj hij
    apply hd i j hj
    intro H
    exact hij (by simp only [Matrix.map_apply, H, map_zero])
  apply FiniteSpanningAnnihilator.charpoly_root_of_relations
    (matrix T normal bound shift) φ a (fun i => v i.val) hne
  intro j
  have H := GradedReductionMatrix.normal_span (T.map φ) normal degree ha' hd' bound hbound v hv (shift j)
  rw [← Matrix.map_pow] at H
  simp only [Matrix.map_apply] at H
  change (∑ i : {i // normal i}, v i.val * φ ((T ^ (bound + 1)) i.val (shift j))) = a * v j.val
  calc
    _ = ∑ i ∈ Finset.univ.filter normal, v i * φ ((T ^ (bound + 1)) i (shift j)) := by
      simpa using (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
        (p := normal) (fun i => v i * φ ((T ^ (bound + 1)) i (shift j))))
    _ = v (shift j) := H.symm
    _ = a * v j.val := hshift j

theorem charpoly_degree [Nontrivial R] (T : Matrix ι ι R) (normal : ι → Prop) (bound : ℕ)
    (shift : {i // normal i} → ι) :
    (matrix T normal bound shift).charpoly.natDegree = Fintype.card {i // normal i} :=
  Matrix.charpoly_natDegree_eq_dim _

/-- Keeping all state indices avoids enumerating a subtype in native matrix
queries. Columns outside the normal set are zero padding. -/
noncomputable def paddedMatrix (T : Matrix ι ι R) (normal : ι → Prop) (bound : ℕ)
    (shift : ι → ι) : Matrix ι ι R :=
  fun i j => if normal j then (T ^ (bound + 1)) i (shift j) else 0

theorem padded_charpoly_root (T : Matrix ι ι R) (normal : ι → Prop) (degree : ι → ℕ)
    (ha : ∀ j, normal j → ∀ i, T i j = if i = j then 1 else 0)
    (hd : ∀ i j, ¬normal j → T i j ≠ 0 → degree i < degree j)
    (bound : ℕ) (hbound : ∀ j, degree j ≤ bound) (shift : ι → ι)
    (φ : R →+* K) (v : ι → K) (hv : v ᵥ* T.map φ = v) (a : K)
    (hshift : ∀ j, normal j → v (shift j) = a * v j) (hne : ∃ i, normal i ∧ v i ≠ 0) :
    (paddedMatrix T normal bound shift).charpoly.eval₂ φ a = 0 := by
  have ha' : ∀ j, normal j → ∀ i, (T.map φ) i j = if i = j then 1 else 0 := by
    intro j hj i
    rw [Matrix.map_apply, ha j hj i]
    split_ifs <;> simp only [map_one, map_zero]
  have hd' : ∀ i j, ¬normal j → (T.map φ) i j ≠ 0 → degree i < degree j := by
    intro i j hj hij
    apply hd i j hj
    intro H
    exact hij (by simp only [Matrix.map_apply, H, map_zero])
  apply FiniteSpanningAnnihilator.charpoly_root_of_relations
    (paddedMatrix T normal bound shift) φ a (fun i => if normal i then v i else 0) ?_ ?_
  · obtain ⟨i, hi, hvi⟩ := hne
    exact ⟨i, by simpa only [ite_eq_left hi] using hvi⟩
  · intro j
    by_cases hj : normal j
    · have H := GradedReductionMatrix.normal_span (T.map φ) normal degree ha' hd' bound hbound v hv (shift j)
      rw [← Matrix.map_pow] at H
      simp only [Matrix.map_apply] at H
      simp only [paddedMatrix, ite_eq_left hj]
      rw [← hshift j hj, H, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp only [zero_mul]
    · simp only [paddedMatrix, ite_eq_right hj, map_zero, mul_zero, Finset.sum_const_zero]

theorem padded_charpoly_degree [Nontrivial R] (T : Matrix ι ι R) (normal : ι → Prop) (bound : ℕ)
    (shift : ι → ι) : (paddedMatrix T normal bound shift).charpoly.natDegree = Fintype.card ι :=
  Matrix.charpoly_natDegree_eq_dim _

end LeanCanny.Algebra.GradedReductionAnnihilator

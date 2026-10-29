/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineHeightPolynomial
public import LeanCanny.Algebra.TriangularPolynomialSystem
public import LeanCanny.Algebra.PartialDerivativeDegree

/-! # Flat critical equations on ancestral affine-height slices

A stage retains n ambient coordinates and n+1 multipliers. Active old heights
are constrained to ancestral polynomials, while unused multipliers are zero.
The source and its derivatives always use the original polynomial. This fixed
2*n+1 layout supports variable slice codimension without repeated elimination.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineCriticalStage
open MvPolynomial
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {ι R : Type*} {n : ℕ} [CommRing R]

abbrev Variables (n : ℕ) := Fin n ⊕ Fin (n + 1)
def ambient (i : Fin n) : ι ⊕ Variables n := Sum.inr (Sum.inl i)
def multiplier (j : Fin (n + 1)) : ι ⊕ Variables n := Sum.inr (Sum.inr j)

theorem variables_card (n : ℕ) : Fintype.card (Variables n) = 2 * n + 1 := by
  simp only [Variables, Fintype.card_sum, Fintype.card_fin]
  omega

noncomputable def gradient (p : MvPolynomial (Fin n) R) (a : Fin (n + 1) → Fin n → R) (i : Fin n) :
    MvPolynomial (ι ⊕ Variables n) R :=
  rename ambient (pderiv i p) - ∑ j, C (a j i) * X (multiplier j)

noncomputable def row (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) :
    Variables n → MvPolynomial (ι ⊕ Variables n) R
  | .inl i => gradient p a i
  | .inr j => Fin.cases (rename ambient p)
      (fun h => if h ∈ s then AffineHeightPolynomial.polynomial (a h.succ) ambient - rename Sum.inl (b h)
        else X (multiplier h.succ)) j

theorem eval_gradient {K : Type*} [CommRing K] (φ : R →+* K)
    (p : MvPolynomial (Fin n) R) (a : Fin (n + 1) → Fin n → R) (z : (ι ⊕ Variables n) → K) (i : Fin n) :
    (gradient p a i).eval₂ φ z = (pderiv i p).eval₂ φ (z ∘ ambient) - ∑ j, φ (a j i) * z (multiplier j) := by
  rw [gradient, eval₂_sub, eval₂_rename]
  simp only [eval₂_sum, eval₂_mul, eval₂_C, eval₂_X]

theorem roots_iff {K : Type*} [CommRing K] (φ : R →+* K)
    (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (z : (ι ⊕ Variables n) → K) :
    (∀ j, (row p s a b j).eval₂ φ z = 0) ↔
      p.eval₂ φ (z ∘ ambient) = 0 ∧
      (∀ j ∈ s, (∑ i, φ (a j.succ i) * z (ambient i)) = (b j).eval₂ φ (z ∘ Sum.inl)) ∧
      (∀ i, (pderiv i p).eval₂ φ (z ∘ ambient) = ∑ j, φ (a j i) * z (multiplier j)) ∧
      ∀ j, j ∉ s → z (multiplier j.succ) = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [row, Fin.cases_zero, eval₂_rename] using h (Sum.inr 0)
    · intro j hj
      simpa only [row, Fin.cases_succ, ite_eq_left hj, eval₂_sub, AffineHeightPolynomial.eval,
        eval₂_rename, sub_eq_zero] using h (Sum.inr j.succ)
    · intro i
      simpa only [row, eval_gradient, sub_eq_zero] using h (Sum.inl i)
    · intro j hj
      simpa only [row, Fin.cases_succ, ite_eq_right hj, eval₂_X] using h (Sum.inr j.succ)
  · rintro ⟨hp, hl, hg, hu⟩ j
    cases j with
    | inl i => simpa only [row, eval_gradient, sub_eq_zero] using hg i
    | inr j =>
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [row, Fin.cases_zero, eval₂_rename] using hp
      · by_cases hj : j ∈ s
        · simpa only [row, Fin.cases_succ, ite_eq_left hj, eval₂_sub, AffineHeightPolynomial.eval,
            eval₂_rename, sub_eq_zero] using hl j hj
        · simpa only [row, Fin.cases_succ, ite_eq_right hj, eval₂_X] using hu j hj

theorem gradient_degree [Nontrivial R] (p : MvPolynomial (Fin n) R) (a : Fin (n + 1) → Fin n → R)
    (i : Fin n) : (gradient (ι := ι) p a i).totalDegree ≤ max p.totalDegree 1 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_rename_le _ _).trans
      (((PartialDerivativeDegree.degree_le _ _).trans (Nat.sub_le _ _)).trans (Nat.le_max_left _ _))
  · have hs : (∑ j : Fin (n + 1), C (a j i) * X (multiplier (ι := ι) j) :
        MvPolynomial (ι ⊕ Variables n) R).totalDegree ≤ 1 := by
      apply totalDegree_finsetSum_le
      intro j _
      exact (totalDegree_mul _ _).trans (by simp)
    exact hs.trans (Nat.le_max_right _ _)

theorem degree_le [Nontrivial R] (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (hb : ∀ j, (b j).totalDegree ≤ 1) (j : Variables n) :
    (row p s a b j).totalDegree ≤ max p.totalDegree 1 := by
  cases j with
  | inl i => exact gradient_degree p a i
  | inr j =>
    refine Fin.cases ?_ (fun j => ?_) j
    · exact (totalDegree_rename_le _ _).trans (Nat.le_max_left _ _)
    · simp only [row, Fin.cases_succ]
      split_ifs
      · exact (totalDegree_sub _ _).trans (max_le
          ((AffineHeightPolynomial.degree_le _ _).trans (Nat.le_max_right _ _))
          ((totalDegree_rename_le _ _).trans ((hb j).trans (Nat.le_max_right _ _))))
      · simpa only [totalDegree_X] using Nat.le_max_right p.totalDegree 1

theorem gradient_mass (p : MvPolynomial (Fin n) ℤ) (a : Fin (n + 1) → Fin n → ℤ)
    (U : ℕ) (ha : ∀ j i, (a j i).natAbs ≤ U) (i : Fin n) :
    MvMass.mass (gradient (ι := ι) p a i) ≤ p.totalDegree * MvMass.mass p + (n + 1) * U := by
  apply (MvMass.sub_le _ _).trans
  apply Nat.add_le_add
  · exact (MvMass.rename_le _ _).trans (MvMass.pderiv_le _ _)
  · apply (MvMass.sum_le _ _).trans
    calc
      _ ≤ ∑ _j : Fin (n + 1), U := Finset.sum_le_sum (fun j _ =>
        (MvMass.mul_le _ _).trans (by simpa only [MvMass.C, MvMass.X, Nat.mul_one] using ha j i))
      _ = (n + 1) * U := by simp

noncomputable def massBound (p : MvPolynomial (Fin n) ℤ) (U B : ℕ) : ℕ :=
  max (max (MvMass.mass p) (p.totalDegree * MvMass.mass p + (n + 1) * U)) (n * U + B + 1)

theorem mass_le (p : MvPolynomial (Fin n) ℤ) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → ℤ) (b : Fin n → MvPolynomial ι ℤ)
    (U B : ℕ) (ha : ∀ j i, (a j i).natAbs ≤ U) (hb : ∀ j, MvMass.mass (b j) ≤ B) (j : Variables n) :
    MvMass.mass (row p s a b j) ≤ massBound p U B := by
  cases j with
  | inl i =>
    exact (gradient_mass p a U ha i).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _))
  | inr j =>
    refine Fin.cases ?_ (fun j => ?_) j
    · exact (MvMass.rename_le _ _).trans ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _))
    · simp only [row, Fin.cases_succ]
      split_ifs
      · apply (MvMass.sub_le _ _).trans
        have H : MvMass.mass (AffineHeightPolynomial.polynomial (a j.succ) (ambient (ι := ι))) +
            MvMass.mass (rename (Sum.inl : ι → ι ⊕ Variables n) (b j)) ≤ n * U + B :=
          Nat.add_le_add (AffineHeightPolynomial.mass_le _ (ambient (ι := ι)) U (ha j.succ))
            ((MvMass.rename_le _ _).trans (hb j))
        exact H.trans ((Nat.le_succ _).trans (Nat.le_max_right _ _))
      · rw [MvMass.X]
        exact (by omega : 1 ≤ n * U + B + 1).trans (Nat.le_max_right _ _)

end LeanCanny.Algebra.FlatAffineCriticalStage

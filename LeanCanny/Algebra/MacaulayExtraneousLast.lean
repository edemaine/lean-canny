/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulaySubtractiveSystem

/-! # The extraneous Macaulay matrix does not use the last polynomial

An unreduced monomial has at least two eligible coordinates. Its least
eligible coordinate therefore cannot be the last coordinate. Every selected
extraneous row uses only a polynomial preceding that last coordinate.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped Classical
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

theorem pivot_ne_last (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : e.degree = level d)
    (hu : Unreduced d e) (last : Fin n) (hlast : ∀ j, j ≤ last) : pivot d e he ≠ last := by
  intro hp
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hu
  have hpi : pivot d e he ≤ i := Finset.min'_le (eligible d e) i hi
  have hpj : pivot d e he ≤ j := Finset.min'_le (eligible d e) j hj
  rw [hp] at hpi hpj
  exact hij ((le_antisymm (hlast i) hpi).trans (le_antisymm (hlast j) hpj).symm)

theorem extraneousMinor_eq_off_last (p q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (last : Fin n) (hlast : ∀ j, j ≤ last) (hpq : ∀ i, i ≠ last → p i = q i) :
    extraneousMinor p d W = extraneousMinor q d W := by
  funext r s
  have hr := (mem_extraneousIndices d W r.val).mp r.property
  change matrix p d W r.val s.val = matrix q d W r.val s.val
  rw [matrix, dite_eq_left hr.1, matrix, dite_eq_left hr.1]
  unfold rowPolynomial
  rw [hpq _ (pivot_ne_last d _ hr.1 hr.2 last hlast)]

theorem extraneousPadded_eq_off_last (p q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (last : Fin n) (hlast : ∀ j, j ≤ last) (hpq : ∀ i, i ≠ last → p i = q i) :
    extraneousPadded p d W = extraneousPadded q d W := by
  funext r s
  by_cases hr : r ∈ extraneousIndices d W
  · have ha := (mem_extraneousIndices d W r).mp hr
    change (if r ∈ extraneousIndices d W then matrix p d W r s else _) =
      (if r ∈ extraneousIndices d W then matrix q d W r s else _)
    rw [ite_eq_left hr, ite_eq_left hr, matrix, dite_eq_left ha.1, matrix, dite_eq_left ha.1]
    unfold rowPolynomial
    rw [hpq _ (pivot_ne_last d _ ha.1 ha.2 last hlast)]
  · simp only [extraneousPadded, PrincipalPadding.matrix, ite_eq_right hr]

theorem extraneousMinor_map (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (extraneousMinor p d W).map φ = extraneousMinor (fun i => (p i).map φ) d W := by
  funext r s
  exact congrFun (congrFun (matrix_map φ p d W) r.val) s.val

theorem activeMinor_map (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (activeMinor p d W).map φ = activeMinor (fun i => (p i).map φ) d W := by
  funext r s
  exact congrFun (congrFun (matrix_map φ p d W) r.val) s.val

theorem det_activeMinor_map (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    φ (activeMinor p d W).det = (activeMinor (fun i => (p i).map φ) d W).det := by
  have h := RingHom.map_det φ (activeMinor p d W)
  change φ (activeMinor p d W).det = ((activeMinor p d W).map φ).det at h
  rw [activeMinor_map] at h
  exact h

theorem det_extraneousMinor_map (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    φ (extraneousMinor p d W).det = (extraneousMinor (fun i => (p i).map φ) d W).det := by
  have h := RingHom.map_det φ (extraneousMinor p d W)
  change φ (extraneousMinor p d W).det = ((extraneousMinor p d W).map φ).det at h
  rw [extraneousMinor_map] at h
  exact h

theorem subtractive_extraneous_eq_off_last (p q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (last : Fin n) (hlast : ∀ j, j ≤ last) (hpq : ∀ i, i ≠ last → p i = q i) :
    extraneousMinor (subtractiveSystem p d) d W = extraneousMinor (subtractiveSystem q d) d W := by
  rw [extraneousMinor_subtractiveSystem, extraneousMinor_subtractiveSystem,
    extraneousMinor_eq_off_last p q d W last hlast hpq]

end LeanCanny.Algebra.Macaulay

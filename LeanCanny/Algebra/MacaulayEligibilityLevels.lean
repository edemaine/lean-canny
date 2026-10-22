/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayActiveCharacteristic
public import LeanCanny.Algebra.MacaulaySubtractiveSystem
public import LeanCanny.Algebra.CharacteristicQuotientDegree

/-! # Macaulay minors by the number of eligible coordinate powers

The level-`h` minor uses active monomials divisible by at least `h`
coordinate powers. Levels one and two recover the existing active and
extraneous determinants. Levels above the arity are empty. All levels
specialize to the identity for coordinate powers.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped Classical Matrix
variable {n : ℕ}

noncomputable def eligibilityIndices (d : Fin n → ℕ) (W h : ℕ) : Finset (Index n W) :=
  Finset.univ.filter (fun r => (FixedWidthPolynomial.vector n W r).degree = level d ∧
    h ≤ (eligible d (FixedWidthPolynomial.vector n W r)).card)

theorem mem_eligibilityIndices (d : Fin n → ℕ) (W h : ℕ) (r : Index n W) :
    r ∈ eligibilityIndices d W h ↔ (FixedWidthPolynomial.vector n W r).degree = level d ∧
      h ≤ (eligible d (FixedWidthPolynomial.vector n W r)).card := by
  simp only [eligibilityIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem eligibilityIndices_one (d : Fin n → ℕ) (W : ℕ) : eligibilityIndices d W 1 = activeIndices d W := by
  ext r
  rw [mem_eligibilityIndices, mem_activeIndices]
  constructor
  · exact And.left
  · intro hr
    exact ⟨hr, Finset.card_pos.mpr (eligible_nonempty d _ hr)⟩

theorem eligibilityIndices_two (d : Fin n → ℕ) (W : ℕ) : eligibilityIndices d W 2 = extraneousIndices d W := by
  ext r
  rw [mem_eligibilityIndices, mem_extraneousIndices]
  unfold Unreduced
  omega

theorem eligibilityIndices_antitone (d : Fin n → ℕ) (W : ℕ) {h k : ℕ} (hk : h ≤ k) :
    eligibilityIndices d W k ⊆ eligibilityIndices d W h := by
  intro r hr
  have he := (mem_eligibilityIndices d W k r).mp hr
  exact (mem_eligibilityIndices d W h r).mpr ⟨he.1, hk.trans he.2⟩

theorem eligibilityIndices_subset_active (d : Fin n → ℕ) (W h : ℕ) : eligibilityIndices d W h ⊆ activeIndices d W := by
  intro r hr
  exact (mem_activeIndices d W r).mpr ((mem_eligibilityIndices d W h r).mp hr).1

theorem eligibilityIndices_eq_empty (d : Fin n → ℕ) (W h : ℕ) (hh : n < h) : eligibilityIndices d W h = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have he := (mem_eligibilityIndices d W h r).mp hr
  have hc : (eligible d (FixedWidthPolynomial.vector n W r)).card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (eligible d (FixedWidthPolynomial.vector n W r))
  omega

variable {R S : Type*} [CommRing R] [CommRing S]

noncomputable def eligibilityMinor (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W h : ℕ) :=
  (matrix p d W).submatrix (fun r : eligibilityIndices d W h => r.val) (fun r : eligibilityIndices d W h => r.val)

theorem eligibilityMinor_det_of_index_eq (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W h : ℕ)
    (s : Finset (Index n W)) (he : eligibilityIndices d W h = s) :
    (eligibilityMinor p d W h).det =
      ((matrix p d W).submatrix (fun r : s => r.val) (fun r : s => r.val)).det := by
  cases he
  rfl

theorem eligibilityMinor_det_one (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (eligibilityMinor p d W 1).det = (activeMinor p d W).det := by
  exact eligibilityMinor_det_of_index_eq p d W 1 _ (eligibilityIndices_one d W)

theorem eligibilityMinor_det_two (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (eligibilityMinor p d W 2).det = (extraneousMinor p d W).det := by
  exact eligibilityMinor_det_of_index_eq p d W 2 _ (eligibilityIndices_two d W)

theorem eligibilityMinor_det_eq_one (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W h : ℕ) (hh : n < h) :
    (eligibilityMinor p d W h).det = 1 := by
  have : IsEmpty (eligibilityIndices d W h) := ⟨fun r => by
    have hr : r.val ∈ (∅ : Finset (Index n W)) := by
      simpa only [eligibilityIndices_eq_empty d W h hh] using r.property
    exact Finset.notMem_empty _ hr⟩
  exact Matrix.det_isEmpty

theorem eligibilityMinor_powers (d : Fin n → ℕ) (W h : ℕ) : eligibilityMinor (powers (R := R) d) d W h = 1 := by
  rw [eligibilityMinor, matrix_powers]
  exact Matrix.submatrix_one _ Subtype.val_injective

theorem eligibilityMinor_subtractiveSystem (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W h : ℕ) :
    eligibilityMinor (subtractiveSystem p d) d W h = AffineCharacteristic.subtractiveMatrix (eligibilityMinor p d W h) :=
  principal_subtractiveSystem p d W (eligibilityIndices d W h) (eligibilityIndices_subset_active d W h)

theorem eligibilityMinor_subtractive_det_ne_zero [IsDomain R] (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W h : ℕ) : (eligibilityMinor (subtractiveSystem p d) d W h).det ≠ 0 := by
  rw [eligibilityMinor_subtractiveSystem]
  exact AffineCharacteristic.subtractive_det_ne_zero _

theorem eligibilityMinor_map (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W h : ℕ) :
    (eligibilityMinor p d W h).map φ = eligibilityMinor (fun i => (p i).map φ) d W h := by
  ext a b
  exact congrFun (congrFun (matrix_map φ p d W) a.val) b.val

theorem det_eligibilityMinor_map (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W h : ℕ) :
    φ (eligibilityMinor p d W h).det = (eligibilityMinor (fun i => (p i).map φ) d W h).det := by
  have he := φ.map_det (eligibilityMinor p d W h)
  change φ (eligibilityMinor p d W h).det = ((eligibilityMinor p d W h).map φ).det at he
  rw [eligibilityMinor_map] at he
  exact he

theorem eligibilityMinor_det_power_specialization (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W h : ℕ) (hp : ∀ i, (p i).map φ = powers (R := S) d i) :
    φ (eligibilityMinor p d W h).det = 1 := by
  rw [det_eligibilityMinor_map, funext hp, eligibilityMinor_powers, Matrix.det_one]

theorem eligibilityMinor_det_ne_zero_of_power_specialization [Nontrivial S] (φ : R →+* S)
    (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W h : ℕ)
    (hp : ∀ i, (p i).map φ = powers (R := S) d i) : (eligibilityMinor p d W h).det ≠ 0 := by
  intro hz
  have he := eligibilityMinor_det_power_specialization φ p d W h hp
  rw [hz, map_zero] at he
  exact zero_ne_one he

end LeanCanny.Algebra.Macaulay
